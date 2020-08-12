(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Permutation.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Init_ext ssrZ ZArith_ext seq_ext uniq_tac encode_decode.
Require Import multi_int integral_type syntax.
Require Import machine_int.
Import MachineInt.
Require Import mips_bipl mips_cmd mips_seplog mips_frame mips_syntax mips_mint.
Import mips_bipl.expr_m.

Declare Scope pseudo_expr_scope.
Declare Scope pseudo_cmd_scope.
Declare Scope pseudo_hoare_scope.
Declare Scope asm_expr_scope.
Declare Scope asm_cmd_scope.
Declare Scope asm_assert_scope.
Declare Scope asm_hoare_scope.
Declare Scope simu_scope.
Declare Scope assoc_scope.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.

Reserved Notation "e1 '\+' e2" (at level 61, left associativity).

Module Simu (A : IntegralType).

Module syntax_m := syntax.Syntax A.

(** Notation for pseudo code *)

Notation "e1 '\+' e2" :=
  (syntax_m.seplog_m.assert_m.expr_m.bop_e syntax_m.seplog_m.assert_m.expr_m.add_e e1 e2)
  : pseudo_expr_scope.
Notation "e1 '\-' e2" :=
  (syntax_m.seplog_m.assert_m.expr_m.bop_e syntax_m.seplog_m.assert_m.expr_m.sub_e e1 e2)
  (at level 61, left associativity) : pseudo_expr_scope.
Notation "e1 '\*' e2" :=
  (syntax_m.seplog_m.assert_m.expr_m.bop_e syntax_m.seplog_m.assert_m.expr_m.mul_e e1 e2)
  (at level 58, left associativity) : pseudo_expr_scope.
Notation "e1 './e' e2" :=
  (syntax_m.seplog_m.assert_m.expr_m.bop_e syntax_m.seplog_m.assert_m.expr_m.div_e e1 e2)
  (at level 75) : pseudo_expr_scope.
Notation "e1 '\%' e2" :=
  (syntax_m.seplog_m.assert_m.expr_m.bop_e syntax_m.seplog_m.assert_m.expr_m.mod_e e1 e2)
  (at level 57, left associativity) : pseudo_expr_scope.
Notation " \| e \|" := (syntax_m.seplog_m.assert_m.expr_m.uop_e syntax_m.seplog_m.assert_m.expr_m.valabs_e e) (at level 57, left associativity) : pseudo_expr_scope.
Notation "e \&& e'" :=
  (syntax_m.seplog_m.assert_m.expr_m.bop_b2 syntax_m.seplog_m.assert_m.expr_m.and_b e e')
  (at level 67, left associativity) : pseudo_expr_scope.
Notation "'.--e' e" :=
  (syntax_m.seplog_m.assert_m.expr_m.uop_e syntax_m.seplog_m.assert_m.expr_m.negate_e e)
  (at level 75) : pseudo_expr_scope.
Notation "e \= e'" :=
  (syntax_m.seplog_m.assert_m.expr_m.bop_b syntax_m.seplog_m.assert_m.expr_m.eq_b e e')
  (at level 64, left associativity) : pseudo_expr_scope.
Notation "e \!= e'" :=
  (syntax_m.seplog_m.assert_m.expr_m.bop_b syntax_m.seplog_m.assert_m.expr_m.neq_b e e')
  (at level 64, left associativity) : pseudo_expr_scope.
Notation "e \>= e'" :=
  (syntax_m.seplog_m.assert_m.expr_m.bop_b syntax_m.seplog_m.assert_m.expr_m.ge_b e e')
  (at level 63, left associativity) : pseudo_expr_scope.
Notation "e \> e'" :=
  (syntax_m.seplog_m.assert_m.expr_m.bop_b syntax_m.seplog_m.assert_m.expr_m.gt_b e e')
  (at level 63, left associativity) : pseudo_expr_scope.
Notation "'[' x ']_' s" := (syntax_m.seplog_m.assert_m.expr_m.store.get x s) (at level 9, format "'[' [  x  ]_ s ']'") : pseudo_expr_scope.
Notation "'[' e ']e_' s" := (syntax_m.seplog_m.assert_m.expr_m.eval e s) (at level 9, format "'[' [  e  ]e_ s ']'") : pseudo_expr_scope.
Notation "'[' e ']b_' s" := (syntax_m.seplog_m.assert_m.expr_m.eval_b e s) (at level 9, format "'[' [  e  ]b_ s ']'") : pseudo_expr_scope.
Delimit Scope pseudo_expr_scope with pseudo_expr.

Notation "'nat_e'" := (syntax_m.seplog_m.assert_m.expr_m.nat_e) : pseudo_expr_scope.
Notation "'var_e'" := (syntax_m.seplog_m.assert_m.expr_m.var_e) : pseudo_expr_scope.

Notation "s -- c ---> t" := (syntax_m.seplog_m.semop_m.exec s c t) (at level 74) : pseudo_cmd_scope.
Notation " s '--' c '---->' t " := (syntax_m.seplog_m.exec0 s c t) (at level 74, no associativity) : pseudo_cmd_scope.
Notation "c ; d" := (while.seq c d) (at level 81, right associativity) : pseudo_cmd_scope.
Notation "'If' e 'Then' c1 'Else' c2" := (while.ifte e c1 c2)
  (at level 200, right associativity, format
"'[v' '[' 'If'  e  'Then' ']' '//'   '[' c1 ']' '//' '[' 'Else' ']' '//'   '[' c2 ']' '//' ']'") : pseudo_cmd_scope.
Notation "'While' e '{{' c '}}' " := (while.while e c)
  (at level 200, format
"'[v' 'While'  e  '{{' '//'   '[' c ']' '//' '}}' ']'") : pseudo_cmd_scope.
Notation "x <- e" := (syntax_m.seplog_m.assign x e) (at level 80) : pseudo_cmd_scope.
Delimit Scope pseudo_cmd_scope with pseudo_cmd.

Notation "'pemp'" := (syntax_m.seplog_m.assert_m.heap.emp) : pseudo_cmd_scope.

Notation "{{ P }} c {{ Q }}" := (syntax_m.seplog_m.hoare_m.hoare P c Q) (at level 82) : pseudo_hoare_scope.
Delimit Scope pseudo_hoare_scope with pseudo_hoare.

(** Notation for assembly code *)

Notation "'var_e'" := (mips_bipl.expr_m.var_e) : asm_expr_scope.
Notation "'[' x ']_' s" := (mips_bipl.store.get x s) (at level 9) : asm_expr_scope.
Notation "'[' e ']e_' s" := (mips_bipl.expr_m.eval e s) (at level 9) : asm_expr_scope.
Notation "'[' e ']b_' s" := (mips_bipl.expr_m.eval_b e s) (at level 9) : asm_expr_scope.
Delimit Scope asm_expr_scope with asm_expr.

Notation "s -- c ---> t" := (WMIPS_Semop.exec s c t) (at level 74, no associativity) : asm_cmd_scope.
Notation "'While' e '{{' c '}}' " := (while.while e c)
  (at level 200, format
"'[v' 'While'  e  '{{' '//'   '[' c ']' '//' '}}' ']'") : asm_cmd_scope.
Notation "'If' e 'Then' c1 'Else' c2" := (while.ifte e c1 c2)
  (at level 200, right associativity, format
"'[v' '[' 'If'  e  'Then' ']' '//'   '[' c1 ']' '//' '[' 'Else' ']' '//'   '[' c2 ']' '//' ']'") : asm_cmd_scope.
(*Notation "s -- c ---> t" := (
while.exec WMIPS_Hoare.store WMIPS_Hoare.heap WMIPS_Hoare.cmd0
      WMIPS_Hoare.exec0 WMIPS_Hoare.expr_b WMIPS_Hoare.eval_b s
c t) (at level 74, no associativity) : asm_cmd_scope.*)
Notation "'If_beq' a ',' b 'Then' x 'Else' y" := (while.ifte (beq a b) x y) (at level 200,
format
"'[v' '[' 'If_beq'  a ',' b  'Then' ']' '//'   '[' x ']' '//' '[' 'Else' ']' '//'   '[' y ']' '//' ']'"
) : asm_cmd_scope.
Notation "'If_bgez' a 'Then' x 'Else' y" := (while.ifte (bgez a) x y) (at level 200,
format
"'[v' '[' 'If_bgez'  a  'Then' ']' '//'   '[' x ']' '//' '[' 'Else' ']' '//'   '[' y ']' '//' ']'"
) : asm_cmd_scope.
Notation "'If_bne' a ',' b 'Then' x 'Else' y" := (while.ifte (bne a b) x y) (at level 200,
format
"'[v' '[' 'If_bne'  a ',' b  'Then' ']' '//'   '[' x ']' '//' '[' 'Else' ']' '//'   '[' y ']' '//' ']'"
) : asm_cmd_scope.

Notation "c ; d" := (while.seq c d) (at level 81, right associativity) : asm_cmd_scope.
Delimit Scope asm_cmd_scope with asm_cmd.

(*Delimit Scope asm_cmd_scope with asm_cmd.*)

Notation "P ** Q" := (assert_m.con P Q) (at level 80, right associativity) : asm_assert_scope.
Notation "! e" := (assert_m.bang e) (at level 4) : asm_assert_scope.
Notation "e1 |~> e2" := (assert_m.mapsto e1 e2) (at level 77) : asm_assert_scope.
Notation "x '|-->' l" := (assert_m.mapstos x l) (at level 77) : asm_assert_scope.
Notation "P //\\ Q" := (while.And _ _ P Q) (at level 80, right associativity) : asm_assert_scope.
Delimit Scope asm_assert_scope with asm_assert.


Notation "{{ P }} c {{ Q }}" := (WMIPS_Hoare.hoare P c Q) (at level 82) : asm_hoare_scope.
Notation "{{ P }} c {{ Q }}" := (while.hoare store.t heap.t cmd0 expr_b
                   (fun (eb : expr_b) (s : store.t * heap.t) =>
                    eval_b eb (fst s)) hoare0
                   P c
                   Q) (at level 82) : asm_hoare_scope.

Delimit Scope asm_hoare_scope with asm_hoare.

(** simulation of programs *)

Notation "'pstore'" := (syntax_m.seplog_m.assert_m.expr_m.store.t) : simu_scope.
Local Open Scope simu_scope.

Definition Rel := pstore -> store.t -> heap.t -> Prop.
(*Notation "'Rel'" := (syntax_m.seplog_m.assert_m.expr_m.store.t -> store.t -> heap.t -> Prop) : simu_scope.*)

Notation "P '/\Rel' Q" := (fun st s h => P st s h /\ Q st s h) (at level 80, right associativity) : simu_scope.

Notation "'pcmd'" := (syntax_m.seplog_m.semop_m.cmd) : simu_scope.

Local Open Scope simu_scope.

(* TODO: ranger les coercions *)

Definition cmd_cmd0_asm : cmd0 -> while.cmd := @while.cmd_cmd0 cmd0 expr_b.
Coercion cmd_cmd0_asm : cmd0 >-> while.cmd.

Definition cmd_cmd0_pseudo : syntax_m.seplog_m.cmd0 -> while.cmd := @while.cmd_cmd0 syntax_m.seplog_m.cmd0 syntax_m.seplog_m.assert_m.expr_m.expr_b.
Coercion cmd_cmd0_pseudo : syntax_m.seplog_m.cmd0 >-> while.cmd.

(** forward simulation *)

Section fwd_sim_sect.

Variable R : Rel.

Definition fwd_sim (P0 : Rel) p c :=
  forall st s h, R st s h -> P0 st s h ->
    forall st', (|_ st, pemp _| -- p ---> |_ st', pemp _|)%pseudo_cmd ->
    exists s' h',
      (|_ s, h _| -- c ---> |_ s', h' _|)%asm_cmd /\ R st' s' h'.

Local Notation "p '<=(' P0 ')' c" := (fwd_sim P0 p c) (at level 50).

Lemma fwd_sim_stren (Q P : Rel) p c : (forall st s h, P st s h -> Q st s h) ->
  p <=( Q ) c -> p <=( P ) c.
Proof.
move=> H H'.
rewrite /fwd_sim.
move=> st s h HR HP s' Hp.
apply (H' st s h HR (H _ _ _ HP) s' Hp).
Qed.

Lemma fwd_sim_assoc_L P p1 p2 p3 c : (p1 ; p2 ; p3)%pseudo_cmd <=( P ) c ->
  ((p1 ; p2) ; p3)%pseudo_cmd <=( P ) c.
Proof.
move=> H st s h HR HP s' Hp.
move: (H st s h HR HP s').
apply syntax_m.seplog_m.semop_prop_m.exec_seq_assoc in Hp.
by move/(_ Hp).
Qed.

Lemma fwd_sim_assoc_R P p c1 c2 c3 : p <=( P ) (c1 ; c2 ; c3)%asm_cmd ->
  p <=( P ) ((c1 ; c2) ; c3)%asm_cmd.
Proof.
move=> H s st h HR HP s' Hp.
case: (H s st h HR HP s' Hp) => [st' [h' H']].
exists st', h'.
split; last by tauto.
apply semop_prop_m.exec_seq_assoc'; tauto.
Qed.

End fwd_sim_sect.

Notation "p '<=(' R ',' P0 ')' c" := (fwd_sim R P0 p c) (at level 50) : simu_scope.

Section equiv_pcode_sect.

Definition equiv_pcode p p' :=
  forall s s', (|_ s _| -- p ---> |_ s' _|)%pseudo_cmd <-> (|_ s _| -- p' ---> |_ s' _|)%pseudo_cmd.

Lemma equiv_pcode_trans a b c :
  equiv_pcode a b -> equiv_pcode b c -> equiv_pcode a c.
Proof.
rewrite /equiv_pcode => a_b b_c s s'; split => [Ha | Hc].
by apply b_c, a_b.
by apply a_b, b_c.
Qed.

Lemma equiv_pcode_sym a b :
  equiv_pcode a b -> equiv_pcode b a.
Proof.
rewrite /equiv_pcode => H s s'; split => H'.
by rewrite H.
by rewrite -H.
Qed.

Lemma equiv_pcode_op A e' (e : syntax_m.seplog_m.assert_m.expr_m.expr) op :
  (forall s, ([op (var_e A) e ]e_
  (syntax_m.seplog_m.assert_m.expr_m.store.upd A [e' ]e_ s s) = [op e' e]e_s))%pseudo_expr ->
  (equiv_pcode
  (A <- e' ; A <- op (var_e A) e)
  (A <- op e' e))%pseudo_expr%pseudo_cmd.
Proof.
move=> Hop.
rewrite /equiv_pcode; case=> [s h] [s' h']; split => HA.
case/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_seq_inv_Some : HA.
case=> [s'' h''] [HA1 HA2].
move/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_cmd0_inv : HA1.
case/syntax_m.seplog_m.exec0_assign_inv => [? ?]; subst h'' s''.
move/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_cmd0_inv : HA2.
case/syntax_m.seplog_m.exec0_assign_inv => [? ?]; subst h' s'.
constructor.
rewrite syntax_m.seplog_m.assert_m.expr_m.store.upd_upd_eq Hop; by constructor.
eapply while.exec_seq.
constructor.
by constructor.
constructor.
move/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_cmd0_inv : HA.
case/syntax_m.seplog_m.exec0_assign_inv => [? ?]; subst h' s'.
set s0 := syntax_m.seplog_m.assert_m.expr_m.store.upd A _ _.
set s1 := syntax_m.seplog_m.assert_m.expr_m.store.upd A _ _.
have -> : s1 = syntax_m.seplog_m.assert_m.expr_m.store.upd A
          ([ op (var_e A) e ]e_ s0)%pseudo_expr s0.
  by rewrite /s0 syntax_m.seplog_m.assert_m.expr_m.store.upd_upd_eq Hop.
by apply syntax_m.seplog_m.exec0_assign.
Qed.

(*Lemma equiv_pcode_op A e' (e : syntax_m.seplog_m.assert_m.expr_m.expr) op :
  (forall s, ([op (var_e A) e ]e_
  (syntax_m.seplog_m.assert_m.expr_m.store.upd A [e' ]e_ s s) = [op e' e]e_s))%pseudo_expr ->
  (equiv_pcode
  (A <- e' ; A <- op (var_e A) e)
  (A <- op e' e))%pseudo_expr%pseudo_cmd.
Proof.
move=> Hop.
rewrite /equiv_pcode; case=> [s h] [s' h']; split => HA.
case/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_seq_inv_Some : HA.
case=> [s'' h''] [HA1 HA2].
move/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_cmd0_inv : HA1.
case/syntax_m.seplog_m.exec0_assign_inv => [? ?]; subst h'' s''.
move/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_cmd0_inv : HA2.
case/syntax_m.seplog_m.exec0_assign_inv => [? ?]; subst h' s'.
constructor.
rewrite syntax_m.seplog_m.assert_m.expr_m.store.upd_upd_eq Hop; by constructor.
eapply while.exec_seq.
constructor.
by constructor.
constructor.
move/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_cmd0_inv : HA.
case/syntax_m.seplog_m.exec0_assign_inv => [? ?]; subst h' s'.
set s0 := syntax_m.seplog_m.assert_m.expr_m.store.upd A _ _.
set s1 := syntax_m.seplog_m.assert_m.expr_m.store.upd A _ _.
have -> : s1 = syntax_m.seplog_m.assert_m.expr_m.store.upd A
          ([ op (var_e A) e ]e_ s0)%pseudo_expr s0.
  by rewrite /s0 syntax_m.seplog_m.assert_m.expr_m.store.upd_upd_eq Hop.
by apply syntax_m.seplog_m.exec0_assign.
Qed.
*)

Lemma equiv_pcode_uop A e' op :
  (forall s, ([op (var_e A) ]e_
  (syntax_m.seplog_m.assert_m.expr_m.store.upd A [e' ]e_ s s) = [op e']e_s))%pseudo_expr ->
  (equiv_pcode
  (A <- e' ; A <- op (var_e A))
  (A <- op e'))%pseudo_expr%pseudo_cmd.
Proof.
move=> Hop.
apply equiv_pcode_op with (op := fun a _ => op a).
exact (syntax_m.seplog_m.assert_m.expr_m.cst_e (A.of_nat 0)).
move=> s /=; by rewrite Hop.
Qed.

Lemma equiv_pcode_example_assign : forall A e e',
  (forall s, [ e ]e_s = [ e' ]e_s)%pseudo_expr ->
  (equiv_pcode (A <- e) (A <- e'))%pseudo_expr%pseudo_cmd.
Proof.
move=> A e e' H; rewrite /equiv_pcode; move => [s h] [s' h']; split => H'.
- move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : H'.
  case/syntax_m.seplog_m.exec0_assign_inv => ? ?; subst.
  rewrite H.
  by do 2 constructor.
- move/syntax_m.seplog_m.semop_prop_m.exec_cmd0_inv : H'.
  case/syntax_m.seplog_m.exec0_assign_inv => ? ?; subst.
  rewrite -H.
  by do 2 constructor.
Qed.

Lemma equiv_pcode_seq a a' b b' :
  equiv_pcode a a' -> equiv_pcode b b' ->
  (equiv_pcode (a ; b) (a' ; b'))%pseudo_cmd.
Proof.
move=> Ha Hb; move=> s s'; split => H.
case/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_seq_inv_Some : H.
case=> [s'' h''] [H1 H2].
apply while.exec_seq with (Some (s'', h'')).
by apply (proj1 (Ha _  _) H1).
by apply (proj1 (Hb _  _) H2).
case/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_seq_inv_Some : H.
case=> [s'' h''] [H1 H2].
apply while.exec_seq with (Some (s'', h'')).
by apply (proj2 (Ha _  _) H1).
by apply (proj2 (Hb _  _) H2).
Qed.

Lemma equiv_pcode_expr A e' (e : syntax_m.seplog_m.assert_m.expr_m.expr) :
  (forall s, [e ]e_ s = [ e' ]e_s)%pseudo_expr ->
  (equiv_pcode (A <- e') (A <- e))%pseudo_expr%pseudo_cmd.
Proof.
move=> H.
rewrite /equiv_pcode; case=> [s h] [s' h']; split => HA.
- move/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_cmd0_inv : HA.
  case/syntax_m.seplog_m.exec0_assign_inv => [? ?]; subst h' s'.
  rewrite -H.
  by do 2 constructor.
- move/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_cmd0_inv : HA.
  case/syntax_m.seplog_m.exec0_assign_inv => [? ?]; subst h' s'.
  rewrite H.
  by do 2 constructor.
Qed.

Lemma equiv_pcode_example A e' :
  (equiv_pcode (A <- e' ; A <- var_e A ./e nat_e 2)
    (A <- e' ./e nat_e 2))%pseudo_expr%pseudo_cmd.
Proof.
apply equiv_pcode_op => s /=.
by rewrite syntax_m.seplog_m.assert_m.expr_m.store.get_upd'.
Qed.

Lemma equiv_pcode_example2 v2 u : u <> v2 ->
  (equiv_pcode
    (v2 <- nat_e 1; v2 <- var_e v2 \- var_e u)
    (v2 <- nat_e 1 \- var_e u))%pseudo_expr%pseudo_cmd.
Proof.
move=> v2_u.
apply equiv_pcode_op => s /=.
rewrite syntax_m.seplog_m.assert_m.expr_m.store.get_upd' syntax_m.seplog_m.assert_m.expr_m.store.get_upd //; by apply/eqP.
Qed.

Lemma equiv_pcode_example3 A e' : (equiv_pcode
  (A <- e' ; A <- .--e var_e A) (A <- .--e e'))%pseudo_expr%pseudo_cmd.
Proof.
apply equiv_pcode_uop => s /=.
by rewrite syntax_m.seplog_m.assert_m.expr_m.store.get_upd'.
Qed.

End equiv_pcode_sect.

Lemma fwd_sim_pcode_equiv R P p p' c : p <=(R, P) c ->
  equiv_pcode p p' -> p' <=(R, P) c.
Proof.
move=> p_c p_p' s st h HR HP s' Hp'.
move: {p_p' Hp'}(proj2 (p_p' _ _) Hp').
by move/(p_c _ _ _ HR HP).
Qed.

(** relational Hoare logic *)

Section rela_hoare_sect.

Definition rela_hoare (P Q : Rel) (p : pcmd) c :=
  forall st s h, P st s h ->
    forall st', (|_ st, pemp _| -- p ---> |_ st', pemp _|)%pseudo_cmd ->
    forall s' h', (|_ s, h _| -- c ---> |_ s', h' _|)%asm_cmd ->
      Q st' s' h'.

Local Notation "p '\~\' c '\:' P '\=>'  Q" := (rela_hoare P Q p c) (at level 80).

Lemma rela_hoare_stren (P' P Q : Rel) p c :
  (forall s st h, P s st h -> P' s st h) ->
  p \~\ c \: P' \=> Q -> p \~\ c \: P \=> Q.
Proof.
move=> H P'_Q s st h HP s' exec_p st' h' exec_c.
apply (P'_Q s st h) => //; by apply H.
Qed.

Lemma rela_hoare_weak (Q' P Q : Rel) p c :
  (forall s st h, Q' s st h -> Q s st h) ->
  p \~\ c \: P \=> Q' -> p \~\ c \: P \=> Q.
Proof.
move=> H P_Q' s st h HP s' exec_p st' h' exec_c.
by apply H, (P_Q' s st h).
Qed.

Lemma rela_hoare_seq (Q' P Q : Rel) p1 p2 c1 c2 :
  ~~ syntax_m.contains_malloc p1 -> ~~ syntax_m.contains_malloc p2 ->
  p1 \~\ c1 \: P \=> Q' -> p2 \~\ c2 \: Q' \=> Q ->
  (p1 ; p2)%pseudo_cmd \~\ (c1 ; c2)%asm_cmd \: P \=> Q.
Proof.
move=> malloc1 malloc2 H1 H2 s st h HP s' exec_pseudo st' h' exec_asm.
case/syntax_m.seplog_m.semop_prop_m.exec_seq_inv_Some : exec_pseudo.
case=> s'' h'' [exec_p1 exec_p2].
move: (syntax_m.no_malloc_heap_invariant _ _ _ exec_p1 malloc1 _ _ _ (refl_equal _) (refl_equal _)) => ?; subst h''.
case/semop_prop_m.exec_seq_inv_Some : exec_asm.
case=> st'' h''_ [exec_c1 exec_c2].
move: (H1 _ _ _ HP _ exec_p1 _ _ exec_c1) => HQ'.
by apply (H2 _ _ _ HQ' _ exec_p2 _ _ exec_c2).
Qed.

Lemma rela_hoare_ifte (P Q : Rel) t p1 p2 a b c1 c2 :
  ~~ syntax_m.contains_malloc p1 -> ~~ syntax_m.contains_malloc p2 ->
  p1 \~\ (a ; c1)%asm_cmd \:
    (fun s st h => P s st h /\ ([t]b_s)%pseudo_expr /\
    forall st' h', (Some (st, h) -- a ---> Some (st', h'))%asm_cmd -> eval_b b st')
    \=> Q ->
  p2 \~\ (a ; c2)%asm_cmd \:
    (fun s st h => P s st h /\ (~~ [t]b_s)%pseudo_expr /\
      forall st' h', (Some (st, h) -- a ---> Some (st', h'))%asm_cmd -> ~~ eval_b b st')
    \=> Q ->
  (while.ifte t p1 p2)%pseudo_cmd \~\ (a ; while.ifte b c1 c2)%asm_cmd \:
  (fun s st h =>
    P s st h /\
    (forall st' h',
      (Some (st, h) -- a ---> Some (st', h'))%asm_cmd ->
      (([t]b_s)%pseudo_expr <->
        mips_bipl.expr_m.eval_b b st')))
  \=> Q.
Proof.
move=> malloc1 malloc2 H1 H2 s st h HP s' exec_pseudo st' h' exec_asm.
case/semop_prop_m.exec_seq_inv_Some : exec_asm.
case=> st'' h'' [exec_a exec_asm].
case/orP : (orbN ([ t ]b_s)%pseudo_expr) => Ht.
- apply syntax_m.seplog_m.semop_prop_m.exec_ifte_true_inv in exec_pseudo => //.
  case/orP : (orbN (eval_b b st'')%pseudo_expr) => Hb.
  + apply semop_prop_m.exec_ifte_true_inv in exec_asm => //.
    apply (H1 s st h) => //.
    split; first by tauto.
    split; first by tauto.
    move=> st'0 h'0 exec_a0.
    by case: (semop_deter_prop_m.exec_deter _ _ _ exec_a _ exec_a0) => ? ?; subst st'0 h'0.
    by econstructor; eauto.
  + case: HP => _.
    case/(_ _ _ exec_a) => X.
    apply X in Ht.
    by rewrite Ht in Hb.
- apply syntax_m.seplog_m.semop_prop_m.exec_ifte_false_inv in exec_pseudo => //.
  case/orP : (orbN (eval_b b st'')) => Hb.
  + case: HP => _.
    case/(_ _ _ exec_a) => _ X.
    apply X in Hb.
    by rewrite Hb in Ht.
  + apply semop_prop_m.exec_ifte_false_inv in exec_asm => //.
    apply (H2 s st h) => //.
    split; first by tauto.
    split; first by tauto.
    move=> st'0 h'0 exec_a0.
    by case: (semop_deter_prop_m.exec_deter _ _ _ exec_a _ exec_a0) => ? ?; subst st'0 h'0.
    by econstructor; eauto.
Qed.

Lemma rela_hoare_ignore_R P Q p c1 c2 :
  p \~\ c2 \: P \=> Q ->
  (forall st h st'' h'',
    (|_ st, h _| -- c1 ---> |_ st'', h'' _|)%asm_cmd ->
    (forall s, P s st h -> P s st'' h'')) ->
  p \~\ (c1 ; c2)%asm_cmd \: P \=> Q .
Proof.
move=> P_Q H.
move=> s st h HP s' exec_p st' h' exec_c1c2.
case/semop_prop_m.exec_seq_inv_Some : exec_c1c2 => [[st'' h''] [Hc1 Hc2]].
apply (P_Q s st'' h'') => //.
by apply (H _ _ _ _ Hc1).
Qed.

End rela_hoare_sect.

Notation "p '\~\' c '\:' P '\=>'  Q" := (rela_hoare P Q p c) (at level 80) : simu_scope.

(** simulation of sequences of commands *)

Lemma fwd_sim_seq Q R p p' c c' P :
  ~~ syntax_m.contains_malloc p -> ~~ syntax_m.contains_malloc p' ->
  p \~\ c \: P \=> Q ->
  p <=(R, P) c -> p' <=(R, Q) c' ->
  (p ; p')%pseudo_cmd <=(R, P) (c ; c')%asm_cmd.
Proof.
move=> Hp Hp' HPQ Hfwd_sim_p Hfwd_sim_p'; move=> s st h HR HP s' Hexec_pp'.
case/syntax_m.seplog_m.semop_prop_m.exec_seq_inv : Hexec_pp' => s'' [Hexec_p Hexec_p'].
destruct s'' as [[s'' h'']|]; last by move/syntax_m.seplog_m.semop_prop_m.from_none : Hexec_p'.
move: (syntax_m.no_malloc_heap_invariant _ _ _ Hexec_p Hp s _ _ (refl_equal _) (refl_equal _)) => Hh''; subst h''.
case: {Hfwd_sim_p}(Hfwd_sim_p _ _ _ HR HP _ Hexec_p) => st'' [h'' [Hexec_c HR'']].
have HQ'' : Q s'' st'' h''.
  rewrite /rela_hoare in HPQ; by apply HPQ with s st h.
case: {Hfwd_sim_p'}(Hfwd_sim_p' _ _ _ HR'' HQ'' _ Hexec_p') => st' [h' [Hexec_c' HR']].
exists st', h'; split; last by [].
by apply while.exec_seq with (Some (st'', h'')).
Qed.

(** partial forward simulation *)

Definition pfwd_sim (R P0 : Rel) (p : pcmd) c := p \~\ c \: (R /\Rel P0) \=> R.

Notation "p '<=p(' R ',' P0 ')' c" := (pfwd_sim R P0 p c) (at level 50) : simu_scope.

Lemma pfwd_sim_stren (R I0' I0 : Rel) p c :
  (forall s st h, I0 s st h -> I0' s st h) ->
  p <=p( R, I0' ) c -> p <=p( R, I0 ) c.
Proof.
move=> H.
apply rela_hoare_stren.
move=> s st h []; by auto.
Qed.

Definition safe_termination (R : Rel) c :=
  forall s st h, R s st h -> exists s', (|_ st, h _| -- c ---> |_ s' _|)%asm_cmd.

Lemma safe_termination_stren (R R': _ -> _ -> _ -> Prop) c :
  (forall s st h, R s st h -> R' s st h) ->
  safe_termination R' c -> safe_termination R c.
Proof.
move=> H H1.
rewrite /safe_termination => s st h HR.
exact: (H1 s st h (H _ _ _ HR)).
Qed.

Lemma safe_termination_pull_out (R : Rel) P c :
  (forall s st h, R s st h -> P) ->
  (P -> safe_termination R c) ->
  safe_termination R c.
Proof.
move=> H1 H2.
rewrite /safe_termination.
move=> s st h HR.
move: (HR).
apply H1 in HR.
apply H2 in HR.
by move/(HR s st h).
Qed.

(** partial forward simulation implies forward simulation *)
Lemma pfwd_sim_fwd_sim (R P0 : Rel) (p : pcmd) c :
  p <=p( R , P0 ) c -> safe_termination (R /\Rel P0) c -> p <=(R, P0) c.
Proof.
move=> Hpfwd_sim Hterm_c s st h HR HP0 s' Hexec_p.
case: (Hterm_c _ _ _ (conj HR HP0)).
move=> [st' h'] Hexec_c.
move: {Hpfwd_sim}(Hpfwd_sim _ _ _ (conj HR HP0) _ Hexec_p _ _ Hexec_c) => Hpfwd_sim.
by exists st', h'.
Qed.

Lemma pfwd_sim_fwd_sim_spec (R P0 : Rel) (p : pcmd) c :
  p <=p( R , P0 ) c -> safe_termination R c -> p <=(R, P0) c.
Proof.
move=> Hpfwd_sim Hterm_c.
apply pfwd_sim_fwd_sim => //.
apply safe_termination_stren with R => //.
by move=> s st h [].
Qed.

(** backward simulation in the sense of Leroy (JAR 2009) *)

Definition bck_sim (R P0 : Rel) (p : syntax_m.seplog_m.semop_m.cmd) (c : WMIPS_Semop.cmd) :=
  forall s st h, R s st h -> P0 s st h ->
    forall st' h', (|_ st, h _| -- c ---> |_ st', h' _|)%asm_cmd ->
      exists s', (|_ s, syntax_m.seplog_m.assert_m.heap.emp _| -- p --->
        |_ s', syntax_m.seplog_m.assert_m.heap.emp _|)%pseudo_cmd /\ R s' st' h'.

Local Notation "c '<=B(' R ',' P0 ')' p" := (bck_sim R P0 p c) (at level 50).

Definition terminating p := forall s, exists s',
  (Some (s, syntax_m.seplog_m.assert_m.heap.emp) -- p --->
    Some (s', syntax_m.seplog_m.assert_m.heap.emp))%pseudo_cmd.

(** forward simulation implies backward simulation *)

Lemma fwd_sim_bck_sim R P0 p c : terminating p -> p <=(R, P0) c -> c <=B(R , P0) p.
Proof.
move=> Hp.
rewrite /fwd_sim /bck_sim => Hfwd_sim_R s st h HR HP0 st' h' Hc.
case: (Classical_Prop.classic (exists s', (Some (s, syntax_m.seplog_m.assert_m.heap.emp) -- p --->
  Some (s', syntax_m.seplog_m.assert_m.heap.emp))%pseudo_cmd /\ ~ R s' st' h')) => X.
- case: X => s' [Hs' HR'].
  move: {Hfwd_sim_R}(Hfwd_sim_R _ _ _ HR HP0 _ Hs') => Hfwd_sim_R.
  case: Hfwd_sim_R => st'_ [h'_ [Hc_ HR'_]].
  by case: (mips_syntax.semop_deter_prop_m.exec_deter _ _ _ Hc _ Hc_) => Hst' Hh'; subst st'_ h'_.
- have {}X : forall s', (~ (Some (s, syntax_m.seplog_m.assert_m.heap.emp) -- p --->
  Some (s', syntax_m.seplog_m.assert_m.heap.emp))%pseudo_cmd) \/ R s' st' h'.
    move/Classical_Pred_Type.not_ex_all_not : X => X s'.
    move/Classical_Prop.not_and_or: {X}(X s').
    case; first by auto.
    right; by apply Classical_Prop.NNPP.
  case: {Hp}(Hp s) => s' Hp.
  case: {X}(X s') => // HR'.
  by exists s'.
Qed.

(** simulation of a boolean expression *)
Definition fwd_sim_b (R : Rel) b pre post :=
  forall st s h, R st s h ->
    exists s', (|_ s, h _| -- pre ---> |_ s', h _|)%asm_cmd /\
      (([ b ]b_ st)%pseudo_expr <-> ([ post ]b_ s')%asm_expr).

Notation "b '<=b(' R ')' p1 ';' p2" := (fwd_sim_b R b p1 p2) (at level 30,
  R at next level, p1 at next level, p2 at next level) : simu_scope.

Lemma fwd_sim_b_pull_out (R : Rel) P e p b :
  (forall s st h, R s st h -> P) ->
  (P -> e <=b( R ) p ; b) ->
  e <=b( R ) p ; b.
Proof.
move=> H1 H2.
rewrite /fwd_sim_b.
move=> s st h HR.
move: (HR).
apply H1 in HR.
apply H2 in HR.
by move/(HR s st h).
Qed.

Definition fwd_sim_b' (R : Rel) b pre post :=
  forall s st he, R s st he ->
    (([ b ]b_ s)%pseudo_expr ->
       exists st', (Some (st, he) -- pre ---> Some (st', he))%asm_cmd /\ eval_b post st') /\
    (~~ ([ b ]b_ s)%pseudo_expr ->
       exists st', (Some (st, he) -- pre ---> Some (st', he))%asm_cmd /\ ~~ eval_b post st').

Lemma fwd_sim_b_fwd_sim_b' R b pre_b post_b :
  b <=b( R ) pre_b ; post_b <-> fwd_sim_b' R b pre_b post_b.
Proof.
rewrite /fwd_sim_b /fwd_sim_b'; split=> Hb s st h.
- case/(Hb _) => st' [Hexec_pre_b [Ht Hf]]; split=> Hyp; exists st'.
  tauto.
  split => //.
  move: Hyp; by apply contra.
- case/(Hb _) => Ht Hf; destruct ([ b ]b_s)%pseudo_expr.
  + case: (Ht (refl_equal _)) => st' ?; exists st'; split; by intuition.
  + case: (Hf (refl_equal _)) => st' Hyp; exists st'; split.
    tauto.
    split => //.
    case: Hyp => _.
    by move/negP.
Qed.

Lemma fwd_sim_b_stren (R R' : Rel) p c bt :
  (forall s st h, R s st h -> R' s st h) ->
  p <=b( R' ) c ; bt -> p <=b( R ) c ; bt.
Proof.
move=> R'R H; rewrite /fwd_sim_b => s st h HR.
by apply (H s st h (R'R _ _ _ HR)).
Qed.

Lemma fwd_sim_b_cond (R : Rel) p p' c bt :
  (forall s st h, R s st h -> ([ p ]b_s = [ p' ]b_s)%pseudo_expr) ->
  p' <=b( R ) c ; bt -> p <=b( R ) c ; bt.
Proof.
move=> Hp H.
rewrite /fwd_sim_b => s st h HR.
case: (H s st h HR) => st' Hst'.
exists st'.
rewrite (Hp _ _ _ HR); tauto.
Qed.

Lemma fwd_sim_b_cond_neg (R : Rel) p p' c bt bt' :
  (forall s st h, R s st h -> ([ p ]b_s = ~~ [ p' ]b_s)%pseudo_expr) ->
  (forall st, ([ bt ]b_ st = ~~ [ bt' ]b_ st)%asm_expr) ->
  p' <=b( R ) c ; bt' -> p <=b( R ) c ; bt.
Proof.
move=> Hp Hbt H.
rewrite /fwd_sim_b => s st h HR.
case: (H s st h HR) => st' Hst'.
exists st'.
rewrite (Hp _ _ _ HR).
rewrite (Hbt st').
split; first by tauto.
split; apply contra; tauto.
Qed.

Definition invariant (R : Rel) (c : while.cmd) :=
  forall st s h, R st s h ->
    forall s' h', (|_ s, h _| -- c ---> |_ s', h' _|)%asm_cmd ->
      R st s' h'.

Lemma invariant_equiv (R R' : Rel) p :
  (forall s st h, R' s st h <-> R s st h) -> invariant R p -> invariant R' p.
Proof.
move=> H R_p.
rewrite /invariant => s st h HR' st' h' exec_p.
rewrite /invariant in R_p.
apply H.
apply R_p with st h => //.
by apply H.
Qed.

(** simulation of while-loops *)

Lemma fwd_sim_while b pre post p c : forall
  (Hnomalloc : ~~ syntax_m.contains_malloc p) R P0,
  invariant (R /\Rel P0) pre ->
  p \~\ c \: (fun st s h => P0 st s h /\ ([ post ]b_ s)%asm_expr /\([ b ]b_ st)%pseudo_expr) \=> P0 ->
  b <=b( R /\Rel P0 ) pre ; post ->
  p <=(R, fun st s h => P0 st s h /\ ([ post ]b_ s)%asm_expr /\ ([ b ]b_ st)%pseudo_expr) c ->
  (While b {{ p }})%pseudo_cmd <=(R, P0) (pre ; While (post) {{ c ; pre }})%asm_cmd.
Proof.
move=> Hnomalloc R P0 Hinv HP0_pc Hsimu_b Hpc.
move=> s st h HR HP0 s'.
move HST : (Some (s, _)) => ST.
move HST' : (Some (s', _)) => ST'.
move Hw : (while.while _ _) => w Hexec_w.
move: Hexec_w b pre post p c Hnomalloc P0 Hinv HP0_pc Hsimu_b Hpc s st h HR HP0 s' HST HST' Hw.
elim => //.
- move=> {ST ST' w} [s h_] ST' ST'' b p Heval_b_s Hexec_p _ Hexec_while IH_while b_ pre post p_ c
    Hnomalloc P0 Hinv HP0_pc Hsimu_b Hpc s_ st h HR HP0 s''.
  case=> X Y; subst s_ h_.
  move=> HST''.
  case=> X Y; subst b_ p_.
  destruct ST' as [[s' h']|]; last by subst ST''; by move/syntax_m.seplog_m.semop_prop_m.from_none : Hexec_while.
  have : h' = syntax_m.seplog_m.assert_m.heap.emp.
    by move: (syntax_m.no_malloc_heap_invariant _ _ _ Hexec_p Hnomalloc s s' h' (refl_equal _) (refl_equal _)).
  move=> Hh'; subst h'.
  move: {IH_while}(IH_while b pre post p c Hnomalloc P0 Hinv HP0_pc Hsimu_b Hpc s') => IH_while.
  case: (Hsimu_b _ _ _ (conj HR HP0)) => st1 [Hexec_pre []].
  move/(_ Heval_b_s) => Heval_b_post_b _.
  have HR1 : R s st1 h.
    exact (proj1 (Hinv s st h (conj HR HP0) _ _ Hexec_pre)).
  rewrite /fwd_sim in Hpc.
  have HP01 : P0 s st1 h /\ eval_b post st1 /\
    syntax_m.seplog_m.assert_m.expr_m.eval_b b s.
    move: (proj2 (Hinv s st h (conj HR HP0) _ _ Hexec_pre)).
    tauto.
  case: {Hpc}(Hpc _ _ _ HR1 HP01 _ Hexec_p) => st2 [h2 [Hc' HR2]].
  have HP02 : P0 s' st2 h2 by apply HP0_pc with s st1 h.
  move: {IH_while}(IH_while st2 h2 HR2 HP02 s'' (refl_equal _) HST'' (refl_equal _)) =>
    [st'' [h'' [Hexec_asm HR'']]].
  exists st'', h''; split; last by [].
  apply while.exec_seq with (Some (st1, h)); first by [].
  apply mips_cmd.semop_prop_m.while_seq'; first by [].
  apply mips_cmd.semop_prop_m.exec_seq_assoc'.
  by apply while.exec_seq with (Some (st2, h2)).
- move=> {ST ST' w} [s h_] b c Hb b_ pre post_b p_ c_ Hnomalloc P0 Hinv
    HP0_p_c_ Hsimu_b Hp_c_ s_ st h HR HP0 s__.
  case=> X Y; subst s_ h_.
  case=> X; subst s__.
  case=> X Y; subst b_ p_.
  case: (Hsimu_b _ _ _ (conj HR HP0)) => st1 [Hexec_pre []] _.
  move/contra.
  move/(_ Hb) => Heval_post_b.
  exists st1, h; split.
  + move/while.exec_seq : Hexec_pre; apply.
    by apply while.exec_while_false.
  + exact (proj1 (Hinv s st h (conj HR HP0) _ _ Hexec_pre)).
Qed.

Lemma fwd_sim_while_alt b pre post p c
  (Hnomalloc : ~~ syntax_m.contains_malloc p) R P0 :
  invariant (R /\Rel P0) pre ->
  b <=b( R /\Rel P0 ) pre ; post ->
  p <=(R /\Rel P0, fun s st h => eval_b post st /\ ([ b ]b_s)%pseudo_expr) c ->
  while.while b p <=(R, P0) (pre ; while.while (post) (c ; pre))%asm_cmd.
Proof.
move=> Hinv Hsimu_b Hpc.
move=> s st h HR HP0 s'.
move HST : (Some (s, _)) => ST.
move HST' : (Some (s', _)) => ST'.
move Hw : (while.while _ _) => w Hexec_w.
move: Hexec_w b pre post p c Hnomalloc P0 Hinv Hsimu_b Hpc s st h HR HP0 s' HST HST' Hw.
elim => //.
- move=> {ST ST' w} [s h_] ST' ST'' b p Heval_b_s Hexec_p _ Hexec_while IH_while b_ pre post p_ c
    Hnomalloc P0 Hinv Hsimu_b Hpc s_ st h HR HP0 s''.
  case=> X Y; subst s_ h_.
  move=> HST''.
  case=> X Y; subst b_ p_.
  destruct ST' as [[s' h']|]; last by subst ST''; by move/syntax_m.seplog_m.semop_prop_m.from_none : Hexec_while.
  have : h' = syntax_m.seplog_m.assert_m.heap.emp.
    by move: (syntax_m.no_malloc_heap_invariant _ _ _ Hexec_p Hnomalloc s s' h' (refl_equal _) (refl_equal _)).
  move=> Hh'; subst h'.
  move: {IH_while}(IH_while b pre post p c Hnomalloc P0 Hinv Hsimu_b Hpc s') => IH_while.
  case: (Hsimu_b _ _ _ (conj HR HP0)) => st1 [Hexec_pre []].
  move/(_ Heval_b_s) => Heval_b_post _.
  have HR1 : R s st1 h.
    exact (proj1 (Hinv s st h (conj HR HP0) _ _ Hexec_pre)).
  rewrite /fwd_sim in Hpc.
  have HP01 : P0 s st1 h /\ eval_b post st1 /\
    syntax_m.seplog_m.assert_m.expr_m.eval_b b s.
    move: (proj2 (Hinv s st h (conj HR HP0) _ _ Hexec_pre)).
    tauto.
  case: (Hpc _ _ _ (conj HR1 (proj1 HP01)) (proj2 HP01) _ Hexec_p) => st2 [h2 [Hc' HR2]].
  move: {IH_while}(IH_while st2 h2 (proj1 HR2) (proj2 HR2) s'' (refl_equal _) HST'' (refl_equal _)) =>
    [st'' [h'' [Hexec_asm HR'']]].
  exists st'', h''; split; last by [].
  apply while.exec_seq with (Some (st1, h)); first by [].
  apply mips_cmd.semop_prop_m.while_seq'; first by [].
  apply mips_cmd.semop_prop_m.exec_seq_assoc'.
  by apply while.exec_seq with (Some (st2, h2)).
- move=> {ST ST' w} [s h_] b c Hb b_ pre post p_ c_ Hnomalloc P0 Hinv
    Hsimu_b Hp_c_ s_ st h HR HP0 s__.
  case=> X Y; subst s_ h_.
  case=> X; subst s__.
  case=> X Y; subst b_ p_.
  case: (Hsimu_b _ _ _ (conj HR HP0)) => st1 [Hexec_pre []] _.
  move/contra/(_ Hb) => Heval_post.
  exists st1, h; split.
  + move/while.exec_seq : Hexec_pre; apply.
    by apply while.exec_while_false.
  + exact (proj1 (Hinv s st h (conj HR HP0) _ _ Hexec_pre)).
Qed.

Lemma fwd_sim_ifte b pre post p1 p2 c1 c2
  (Hnomalloc1 : ~~ syntax_m.contains_malloc p1) (Hnomalloc2 : ~~ syntax_m.contains_malloc p2) R P0 :
  invariant (R /\Rel P0) pre ->
  b <=b( R /\Rel P0 ) pre ; post ->
  p1 <=(R, fun st s h => P0 st s h /\ ([ post ]b_ s)%asm_expr /\ ([ b ]b_ st)%pseudo_expr) c1 ->
  p2 <=(R, fun st s h => P0 st s h /\ ~~ ([ post ]b_ s)%asm_expr /\ ~~ ([ b ]b_ st)%pseudo_expr) c2 ->
  (If b Then p1 Else p2)%pseudo_cmd <=(R, P0) (pre ; If post Then c1 Else c2)%asm_cmd.
Proof.
move=> Hinv Hsimu_b Hp1c1 Hp2c2.
move=> s st h HR HP0 s'.
move HST : (Some (s, _)) => ST.
move HST' : (Some (s', _)) => ST'.
move Hp : (while.ifte _ _ _) => p Hexec_p.
move: Hexec_p b pre post p1 p2 c1 c2 Hnomalloc1 Hnomalloc2 P0 Hinv Hsimu_b Hp1c1 Hp2c2 s st h HR HP0 s' HST HST' Hp.
elim => //.
- move=> {ST ST' p} [s h_] ST1 b p1 p2 Heval_b_s Hexec_p1 _ b_ pre post p1_ p2_ c1 c2
    Hnomalloc1 Hnomalloc2 P0 Hinv Hsimu_b Hp1c1 Hp2c2 s_ st h HR HP0 s''.
  case=> ? ?; subst s_ h_.
  move=> HST''.
  case=> ? ? ?; subst b_ p1_ p2_.
  destruct ST1 as [[s1 h1]|]; last by [].
  have : h1 = syntax_m.seplog_m.assert_m.heap.emp.
    by move: (syntax_m.no_malloc_heap_invariant _ _ _ Hexec_p1 Hnomalloc1 s s1 h1 (refl_equal _) (refl_equal _)).
  move=> ?; subst h1.
  case: HST'' => ?; subst s''.
  case: (Hsimu_b _ _ _ (conj HR HP0)) => st1 [Hexec_pre []].
  move/(_ Heval_b_s) => Heval_b_post _.
  have HR1 : R s st1 h by exact (proj1 (Hinv s st h (conj HR HP0) _ _ Hexec_pre)).
  rewrite /fwd_sim in Hp1c1.
  have HP01 : P0 s st1 h /\ eval_b post st1 /\ ([ b ]b_s)%pseudo_expr.
    have HP01 : P0 s st1 h.
      exact (proj2 (Hinv s st h (conj HR HP0) _ _ Hexec_pre)).
    tauto.
  case: {Hp1c1}(Hp1c1 _ _ _ HR1 HP01 _ Hexec_p1) => st2 [h2 [Hc' HR2]].
  exists st2, h2; split; last by [].
  apply while.exec_seq with (Some (st1, h)) => //.
  by apply while.exec_ifte_true.
- move=> {ST ST' p} [s h_] ST2 b p1 p2 Heval_b_s Hexec_p1 _ b_ pre post p1_ p2_ c1 c2
    Hnomalloc1 Hnomalloc2 P0 Hinv Hsimu_b Hp1c1 Hp2c2 s_ st h HR HP0 s''.
  case=> ? ?; subst s_ h_.
  move=> HST''.
  case=> ? ? ?; subst b_ p1_ p2_.
  destruct ST2 as [[s2 h2]|]; last by [].
  have : h2 = syntax_m.seplog_m.assert_m.heap.emp.
    by move: (syntax_m.no_malloc_heap_invariant _ _ _ Hexec_p1 Hnomalloc2 s s2 h2 (refl_equal _) (refl_equal _)).
  move=> ?; subst h2.
  case: HST'' => ?; subst s''.
  case: (Hsimu_b _ _ _ (conj HR HP0)) => st2 [Hexec_pre []] _.
  move/contra/(_ Heval_b_s) => Heval_b_post.
  have HR2 : R s st2 h.
    exact (proj1 (Hinv s st h (conj HR HP0) _ _ Hexec_pre)).
  rewrite /fwd_sim in Hp2c2.
  have HP02 : P0 s st2 h /\ ~~ eval_b post st2 /\ ~~ ([ b ]b_s)%pseudo_expr.
    by move: (proj2 (Hinv s st h (conj HR HP0) _ _ Hexec_pre)) => HP01.
  case: {Hp2c2}(Hp2c2 _ _ _ HR2 HP02 _ Hexec_p1) => st1 [h1 [Hc' HR2_]].
  exists st1, h1; split; last by [].
  apply while.exec_seq with (Some (st2, h)) => //.
  by apply while.exec_ifte_false.
Qed.

Lemma fwd_sim_ifte_spec b pre post p1 p2 c1 c2
  (Hnomalloc1 : ~~ syntax_m.contains_malloc p1) (Hnomalloc2 : ~~ syntax_m.contains_malloc p2) R P0 :
  invariant (R /\Rel P0) pre ->
  b <=b( R ) pre ; post ->
  p1 <=(R, fun s st h => P0 s st h /\ ([ post ]b_ st)%asm_expr /\ ([ b ]b_s)%pseudo_expr) c1 ->
  p2 <=(R, fun s st h => P0 s st h /\ ~~ ([ post ]b_ st)%asm_expr /\ ~~ ([ b ]b_s)%pseudo_expr) c2 ->
  (If b Then p1 Else p2)%pseudo_cmd <=(R, P0) (pre ; If post Then c1 Else c2)%asm_cmd.
Proof.
move=> Hinv Hsimu_b Hp1c1 Hp2c2.
apply fwd_sim_ifte => //.
move=> fwd_sim_b st h R_P0.
apply Hsimu_b.
by case: R_P0.
Qed.

End Simu.

Module heap_tac_m := finmap.Map_Tac heap.

Module Import simu_m := Simu ZIT.

Notation "p '<=(' R ',' P0 ')' c" := (fwd_sim R P0 p c) (at level 50) : simu_scope.

Local Open Scope simu_scope.

Lemma fwd_sim_nop R I0 : syntax_m.seplog_m.skip <=(R, I0) nop.
Proof.
rewrite /fwd_sim. move=> s st h HR HI0 s'.
move/syntax_m.seplog_m.hoare_prop_m.while_semop_prop_m.exec_cmd0_inv.
inversion 1; subst.
exists st, h; split; [by do 2 constructor | exact HR].
Qed.

(** * relation between a pseudo-code variable and an asm mult_int *)

(** memory int: multi-precision integers pointed to by registers *)
Inductive mint : Type :=
| unsign : reg -> reg -> mint
| signed : nat -> reg -> mint.

Definition mintP (t1 t2 : mint) : bool :=
  match t1, t2 with
    | unsign r1 r1', unsign r2 r2' => regP r1 r2 && regP r1' r2'
    | signed l1 r1, signed l2 r2 => beq_nat l1 l2 && regP r1 r2
    | _, _ => false
  end.

Lemma mintP_eq : forall n m, mintP n m -> n = m.
Proof.
case=> // [u1 u1'|l1 s1] // [u2 u2'|l2 s2] //= H.
- case/andP : H; move/eqP=> ->; by move/eqP=> ->.
- case/andP : H.
  move/beq_nat_true => ->.
  by move/eqP => ->.
Qed.

Lemma mintP_refl : forall n, mintP n n.
Proof.
case=> [r1 r1'|l1 s1] /=.
- apply/andP; split; by apply/eqP.
- rewrite -beq_nat_refl /=; by apply/eqP.
Qed.

Lemma eqmintP : Equality.axiom mintP.
Proof.
move=> n m. apply: (iffP idP) => [H | <-].
- move: (mintP_eq n m); tauto.
- by rewrite mintP_refl.
Qed.

Canonical Structure mint_eqMixin := EqMixin eqmintP.
Canonical Structure mint_eqType := Eval hnf in EqType _ mint_eqMixin.

Definition mint_regs t :=
  match t with
    | unsign rk rx => rk :: rx :: nil
    | signed n rx => rx :: nil
  end.

Lemma mint_regs_unsigned1 a b : List.In a (mint_regs (unsign a b)).
Proof. move=> /=; by auto. Qed.

Lemma mint_regs_unsigned2 a b : List.In a (mint_regs (unsign b a)).
Proof. move=> /=; by auto. Qed.

Definition mints_regs d := flatten (map mint_regs d).

Lemma In_mints_regs : forall d rx t, List.In rx (mint_regs t) -> List.In t d ->
  List.In rx (mints_regs d).
Proof.
elim=> // h t IH rx [rk ry|l ry] /=.
- case.
  + move=> ?; subst rx.
    case=> [-> | H]; apply List.in_or_app.
    * left; rewrite /=. by intuition.
    * right; apply: (IH _ _ _ H); rewrite /=; by intuition.
  + case=> // ?; subst ry.
    case=> [->|H]; apply List.in_or_app.
    * left; rewrite /=; by intuition.
    * right; apply: (IH _ _ _ H) => /=; by intuition.
- case=> // ?; subst rx.
  case=> [->|H]; apply List.in_or_app.
  + left; by rewrite /=; intuition.
  + right; apply: (IH _ _ _ H) => /=; by intuition.
Qed.

Lemma inc_mint_regs : forall d r, r \in d -> inc (mint_regs r) (mints_regs d).
Proof.
elim => // h t IH r; rewrite in_cons => /orP[/eqP ->|rt].
  by rewrite /mints_regs /= inc_app_L.
rewrite /mints_regs /=.
move: (IH _ rt) => /inc_trans; apply.
by rewrite inc_app_R.
Qed.

Lemma Permutation_mints_regs : Permutation_preserving mints_regs.
Proof.
rewrite /Permutation_preserving.
induction 1 => /=.
- by apply Permutation_refl.
- by apply Permutation_app_head.
- rewrite /mints_regs /= !catA; by apply Permutation_app_tail, Permutation_app_swap.
- by eapply Permutation_trans; eauto.
Qed.

Definition mint_ptr t := match t with unsign _ rx => rx | signed _ rx => rx end.

Lemma uniq_mint_ptr : forall l, uniq (map mint_ptr l) -> uniq l.
Proof.
elim=> // hd tl IH /=.
case/andP => H1 H2.
apply/andP.
split; last by auto.
move/negP : H1 => H1.
apply/negP.
contradict H1.
apply/mapP; by exists hd.
Qed.

Lemma not_In_mint_ptr : forall l t, ~ List.In (mint_ptr t) (map mint_ptr l) -> ~ List.In t l.
Proof.
elim=> // h t IH ty /= X.
contradict X; case : X => [<-|X].
- by left.
- move: {IH}(IH ty); tauto.
Qed.

(** sign-magnitude representation *)

Local Open Scope multi_int_scope.

Lemma max_val (l : list (int 32)) n : size l = n ->
  forall val l, val = sgZ val * @lSum 32 n l (*\S_{ n } l TODO *) ->
    `| val | < \B^n.
Proof.
move=> l_n val val_l ->.
destruct val.
- exact/Zbeta_gt0.
- rewrite [sgZ _]/= mul1Z Z.abs_eq.
  by apply max_lSum.
  by apply min_lSum.
- rewrite [sgZ _]/= Zabs_non_eq mulN1Z.
  rewrite oppZK; exact: max_lSum.
  rewrite leZ_oppl oppZ0; exact/min_lSum.
Qed.

Local Open Scope simu_scope.

Definition var_mint (x : bipl.var.v) (mx : mint) : Rel := fun st s h =>
  match mx with
    | unsign rk rx =>
      var_unsign (Z.abs_nat (u2Z ([ rk ]_ s))%asm_expr) rx ([ x ]_ st)%pseudo_expr s h
    | signed nk rx =>
      var_signed nk rx ( [ x ]_ st )%pseudo_expr s h
  end.

Lemma var_mint_invariant_unsign : forall x rk rx s s' st st' h,
  ([ rx ]_ st = [ rx ]_ st')%asm_expr -> ([ rk ]_ st = [ rk ]_ st')%asm_expr ->
  ([ x ]_s = [ x ]_s')%pseudo_expr ->
  var_mint x (unsign rk rx) s st h ->
  var_mint x (unsign rk rx) s' st' h.
Proof.
move=> x rk rx_ s s' st st' h Hrx Hrk Hx [].
rewrite Hrk Hx Hrx => Hfit Hover Hmem.
apply mkVarUnsign; [tauto | tauto | ].
move: Hmem; by apply assert_m.mapstos_ext.
Qed.

Lemma var_mint_invariant_signed : forall x nk rx s s' st st' h,
  ([ rx ]_ st = [ rx ]_ st')%asm_expr -> ([ x ]_s = [ x ]_s')%pseudo_expr ->
  var_mint x (signed nk rx) s st h ->
  var_mint x (signed nk rx) s' st' h.
Proof.
move=> x nk rx s s' st st' h Hrx Hx.
rewrite /var_mint.
case=> slen ptr A rx_fit Hencoding ptr_fit mem.
apply (mkVarSigned _ _ _ _ _ slen ptr A) => //.
- by rewrite -Hrx.
- by rewrite -Hx.
- move: mem; apply assert_m.monotony => h'; by apply assert_m.mapstos_ext.
Qed.

Lemma var_mint_invariant : forall (x : bipl.var.v) t (s s' : pstore)
  (st st' : store.t) (h : heap.t),
  (forall rx, List.In rx (mint_regs t) -> [rx ]_ st = [rx ]_ st')%asm_expr ->
  ([x ]_ s = [x ]_ s')%pseudo_expr ->
  var_mint x t s st h -> var_mint x t s' st' h.
Proof.
move=> x [rk rx | nk rx] s s' st st' h H1 H2.
- apply var_mint_invariant_unsign => //.
  apply H1. simpl. by intuition.
  apply H1. simpl. by intuition.
- apply var_mint_invariant_signed => //.
  apply H1. simpl. by intuition.
Qed.

Notation "k '\d\' m" := (heap.dif k m) (at level 69, format "k  '\d\'  m") : heap_scope.
Notation "k '\U' m" := (heap.union k m) (at level 69, format "k  '\U'  m") : heap_scope.
Notation "k '#' m" := (heap.disj k m) (at level 79, format "k  '#'  m") : heap_scope.
Notation "k '\D\' m" := (heap.difs k m) (at level 69, format "k  '\D\'  m") : heap_scope.
Notation "k '|P|' m" := (heap.proj k m) (at level 69, format "k  '|P|'  m") : heap_scope.
Local Open Scope heap_scope.

Definition heap_cut h (x : heap.l) (k : nat) := h |P| iota x k.

Definition heap_mint (t : mint) (st : store.t) h : heap.t :=
  match t with
    | unsign rk rx =>
      (heap_cut h '|u2Z [rx]_st / 4| '|u2Z [rk]_st|)%asm_expr
    | signed nk rx =>
      let olen := heap.get (Z.abs_nat (u2Z [rx]_st / 4))%asm_expr h in
      let optr := heap.get (Z.abs_nat (u2Z ([rx ]_ st `+ four32) / 4))%asm_expr h in
      match olen, optr with
        | Some len, Some ptr =>
          heap_cut h (Z.abs_nat (u2Z [rx]_st / 4))%asm_expr 2 \U
          heap_cut h (Z.abs_nat (u2Z ptr / 4)) nk
        | _, _ => h
      end
  end.

Lemma var_mint_length_heap_to_list x s rk rx st h :
  var_mint x (unsign rk rx) s st (heap_mint (unsign rk rx) st h)%asm_expr ->
  (size (heap2list (Z.abs_nat (u2Z ([rx ]_ st) / 4)) (Z.abs_nat (u2Z ([rk ]_ st))) h) =
  Z.abs_nat (u2Z ([rk ]_ st)))%asm_expr.
Proof.
move=> H.
rewrite len_heap2list //.
case: H => Hfit Hover.
move/assert_m.mapstos_inv_dom.
rewrite size_Z2ints => /(_ Hfit) ->.
apply/seq_ext.incP.
by rewrite heap.inc_dom_proj_dom.
Qed.

Lemma var_signed_exists_get_ptr x nk rx s st h :
  var_mint x (signed nk rx) s st h ->
  exists ptr, heap.get (Z.abs_nat (u2Z ([rx]_st `+ four32)%asm_expr / 4)) h = Some ptr /\
    u2Z ptr + 4 * Z_of_nat nk < \B^1.
Proof.
case=> slen ptr A rx_fit encodingA ptr_fit Hmem.
exists ptr.
rewrite !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh1 => p [Hp Hh1].
rewrite Hp h1_U_h2.
split; last by [].
apply heap.get_union_L => //.
by rewrite Hh1 mulZC Z_div_mult_full // Zabs2Nat.id heap.get_sing.
Qed.

Lemma var_signed_exists_get_slen x nk rx s st h :
  var_mint x (signed nk rx) s st h ->
  exists slen, heap.get (Z.abs_nat (u2Z ([rx]_st)%asm_expr / 4)) h = Some slen /\
    s2Z slen = sgZ (s2Z slen) * Z_of_nat nk.
Proof.
case=> slen ptr A rx_fit encoding ptr_fit /= Hmem.
exists slen.
rewrite !assert_m.conAE in Hmem.
case: Hmem => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh1 => p [Hp Hh1].
rewrite Hp h1_U_h2.
split.
  apply heap.get_union_L => //.
  by rewrite Hh1 mulZC Z_div_mult_full // Zabs2Nat.id heap.get_sing.
by case: encoding.
Qed.

(* TODO: useful? move *)
Lemma var_signed_ptr_fit x nk rx s st h :
  var_mint x (signed nk rx) s st (heap_mint (signed nk rx) st h) ->
  u2Z ([ rx ]_st)%asm_expr + 4 * 2 < \B^1.
Proof. by case. Qed.

Module heap_prop_m := finmap.Map_Prop heap.

Lemma con_heap_mint_signed_con_TT st h nk rx Q P :
  (Q ** P)%asm_assert st (heap_mint (signed nk rx) st h) ->
  (Q ** assert_m.TT)%asm_assert st h.
Proof.
move=> [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
exists h1, (h \D\ heap.dom h1).
split; first by apply heap.disj_difs', seq_ext.inc_refl.
split; last by [].
rewrite /= in h1Uh2; move: h1Uh2.
move Heq : (heap.get '|u2Z ([rx ]_ st)%asm_expr / 4| h) => [slen'|]; last first.
  move=> ->; rewrite heap.difs_union_L; last by rewrite -heap.disjE; by apply heap.disj_sym.
  by rewrite heap.difs_self heap.unioneh.
move Heq2 : (heap.get '|u2Z (([rx ]_ st)%asm_expr `+ four32) / 4| h) => [ptr'|]; last first.
  move=> ->; rewrite heap.difs_union_L; last by rewrite -heap.disjE; by apply heap.disj_sym.
  by rewrite heap.difs_self heap.unioneh.
move=> H0.
apply heap.union_difsK; last by [].
have : heap.inclu h1 (h1 \U h2) by apply heap.inclu_union_L => //; apply heap.inclu_refl.
rewrite -H0 -heap.proj_app.
by move/heap.proj_inclu.
Qed.

Lemma con_heap_mint_unsign_cons (r rk : reg_eqType) (A : seq (int 32)) (st : store.t) h h' :
  heap.inclu h' h ->
  u2Z ([ r ]_ st)%asm_expr + 4 * Z.of_nat (size A) < \B^1 ->
  (Z.abs_nat (u2Z [ rk ]_ st))%asm_expr = size A ->
  (var_e%asm_expr r |--> A)%asm_assert st h' ->
  (var_e%asm_expr r |--> A)%asm_assert st (heap_mint (unsign rk r) st h).
Proof.
move=> h'h Hr rk_L Hh'.
rewrite /heap_mint /heap_cut.
move/assert_m.mapstos_inv_dom : (Hh').
move/(_ Hr) => Htmp.
rewrite rk_L Htmp.
by rewrite (proj1 (heap.incluE _ _) h'h).
Qed.

Lemma con_heap_mint_signed_cons r slen ptr A st h h' L :
  heap.inclu h' h ->
  u2Z ([r ]_ st)%asm_expr + 4 * 2 < \B^1 ->
  u2Z ([int_e ptr ]e_ st)%asm_expr + 4 * Z_of_nat (size A) < Zbeta 1 ->
  size A = L ->
  (var_e r |--> slen :: (ptr :: List.nil) ** int_e ptr |--> A)%asm_expr%asm_assert st
    h' ->
  (var_e r |--> slen :: (ptr :: List.nil) ** int_e ptr |--> A)%asm_expr%asm_assert st
    (heap_mint (signed L r) st h).
Proof.
move=> h'_h r_fit ptr_fit A_L Hh'.
have K1 : heap.get (Z.abs_nat (u2Z ([r ]_ st)%asm_expr / 4)) h = Some slen.
  apply heap.inclu_get with h' => //.
  by apply assert_m.mapstos_get1 in Hh'.
have K2 : heap.get (Z.abs_nat (u2Z ([r ]_ st `+ four32)%asm_expr / 4)) h = Some ptr.
  apply heap.inclu_get with h' => //.
  by apply assert_m.mapstos_get2 in Hh'.
rewrite [heap_mint _ _ _]/= K1 K2.
set hh := _ \U _.
suff : hh = h' by move=> ->.
rewrite /hh.
case: Hh' => h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
rewrite /heap_cut.
apply assert_m.mapstos_inv_dom in Hh1 => //.
rewrite Hh1.
apply assert_m.mapstos_inv_dom in Hh2 => //.
rewrite -A_L Hh2 /hh /heap_cut h1_U_h2.
congr (_ \U _).
- apply heap.incluE.
  apply heap_prop_m.inclu_union_inv_L with h2 => //.
  apply heap.inclu_trans with h' => //.
  rewrite -h1_U_h2; by apply heap.inclu_refl.
- apply heap.incluE.
  apply heap_prop_m.inclu_union_inv_L with h1 => //.
  by apply heap.disj_sym.
  rewrite heap.unionC; last by apply heap.disj_sym.
  apply heap.inclu_trans with h' => //.
  rewrite -h1_U_h2; by apply heap.inclu_refl.
Qed.

Lemma heap_mint_signed_proj st h nk rA ptrA lenA :
  (var_e rA |--> lenA :: ptrA :: nil ** assert_m.TT)%asm_expr%asm_assert st (heap_mint (signed nk rA) st h) ->
  heap_mint (signed nk rA) st h = h |P| seq.cat
    (List.seq (Z.abs_nat (u2Z ([rA ]_ st)%asm_expr / 4)) 2)
    (List.seq (Z.abs_nat (u2Z ([ int_e ptrA ]e_ st)%asm_expr / 4)) nk).
Proof.
move=> mem.
rewrite [assert_m.mapstos _ _]/= in mem.
move/con_heap_mint_signed_con_TT : (mem).
rewrite mips_bipl.assert_m.conAE.
move/mips_bipl.assert_m.mapsto_con_get.
rewrite [heap_mint _ _ _]/= => ->.
move/con_heap_mint_signed_con_TT : mem.
rewrite mips_bipl.assert_m.conAE mips_bipl.assert_m.conCE 2!mips_bipl.assert_m.conAE.
move/mips_bipl.assert_m.mapsto_con_get => ->.
by rewrite /heap_cut -heap.proj_app.
Qed.

Lemma var_mint_unsign_dom_heap_mint x s rk rx st h :
  var_mint x (unsign rk rx) s st (heap_mint (unsign rk rx) st h) ->
  heap.dom (heap_mint (unsign rk rx) st h) =
  (iota (Z.abs_nat (u2Z ([rx ]_ st) / 4)) (Z.abs_nat (u2Z ([rk ]_ st))))%asm_expr.
Proof.
move=> [Hfit Hover Hheap].
apply assert_m.mapstos_inv_dom in Hheap => //; last by rewrite size_Z2ints.
rewrite size_Z2ints in Hheap.
by rewrite Hheap /heap_cut /heap_mint.
Qed.

(* TODO: useful? *)
Lemma heap_inclu_heap_mint_unsign h st nk rx : heap.inclu (heap_mint (unsign nk rx) st h) h.
Proof. by apply heap.inclu_proj. Qed.

Lemma heap_inclu_heap_mint_signed h st nk rx : heap.inclu (heap_mint (signed nk rx) st h) h.
Proof.
rewrite /=.
set a := heap.get _ _.
destruct a as [a|]; last by apply heap.inclu_refl.
set b := heap.get _ _.
destruct b as [b|]; last by apply heap.inclu_refl.
rewrite /heap_cut.
by apply heap_prop_m.inclu_union; apply heap.inclu_proj.
Qed.

Lemma heap_get_heap_mint_inv x s h : forall t y,
  heap.get x (heap_mint t s h) = Some y -> heap.get x h = Some y.
Proof.
move=> [rk rx | nk rx] y /= H.
- rewrite /heap_cut in H.
  move/heap_prop_m.get_proj_Some_inv : (H) => H'.
  by rewrite heap.get_proj in H.
- move: H.
  move H1 : (heap.get (Z.abs_nat (u2Z ([rx ]_ s)%asm_expr / 4)) _) => [a|] //.
  move H2 : (heap.get (Z.abs_nat (u2Z (([rx ]_ s)%asm_expr `+ four32) / 4)) _) => [b|] //.
  case/heap.get_union_Some_inv => H.
  + move/heap_prop_m.get_proj_Some_inv : (H) => H'.
    by rewrite heap.get_proj in H.
  + move/heap_prop_m.get_proj_Some_inv : (H) => H'.
    by rewrite heap.get_proj in H.
Qed.

Lemma heap_mint_signed_store_invariant st' st h n s : ([ s ]_ st = [ s ]_ st')%asm_expr ->
  heap_mint (signed n s) st h = heap_mint (signed n s) st' h.
Proof. move=> H; by rewrite /heap_mint -H. Qed.

Lemma heap_mint_unsign_store_invariant st' st h rk rx :
  ([ rk ]_ st = [ rk ]_ st')%asm_expr -> ([ rx ]_ st = [ rx ]_ st')%asm_expr ->
  heap_mint (unsign rk rx) st h = heap_mint (unsign rk rx) st' h.
Proof. move=> Hrk Hrx; by rewrite /heap_mint -Hrk -Hrx. Qed.

Lemma heap_mint_store_invariant st' st h t :
  (forall x, List.In x (mint_regs t) -> ([x ]_ st = [x ]_ st')%asm_expr) ->
  heap_mint t st h = heap_mint t st' h.
Proof.
move=> Ht.
destruct t as [rk rx|rx].
apply heap_mint_unsign_store_invariant; apply Ht; simpl; by intuition.
apply heap_mint_signed_store_invariant; apply Ht; simpl; by intuition.
Qed.

Lemma dom_heap_mint_unsign_state_invariant h h' rk rx st st' x s :
  ([rk ]_ st = [rk ]_ st')%asm_expr ->
  ([rx ]_ st = [rx ]_ st')%asm_expr ->
  var_mint x (unsign rk rx) s st (heap_mint (unsign rk rx) st h) ->
  heap.dom h = heap.dom h' ->
  heap.dom (heap_mint (unsign rk rx) st h) = heap.dom (heap_mint (unsign rk rx) st' h').
Proof.
move=> Hrk Hrx_invariant Hnew H_h_h' /=.
rewrite -Hrx_invariant -Hrk /heap_cut.
have Htmp' : (iota (Z.abs_nat (u2Z ([rx ]_ st) / 4)) (Z.abs_nat (u2Z ([rk ]_ st))))%asm_expr =
  heap.dom (heap_cut h (Z.abs_nat (u2Z ([rx ]_ st) / 4)) (Z.abs_nat (u2Z ([rk ]_ st))))%asm_expr.
  case : Hnew => Hfit Hover Hmem.
  apply assert_m.mapstos_inv_dom in Hmem => //; last by rewrite size_Z2ints.
  rewrite size_Z2ints in Hmem.
  by rewrite Hmem /heap_cut /heap_mint.
have Htmp'' : (iota (Z.abs_nat (u2Z ([rx ]_ st') / 4)) (Z.abs_nat (u2Z ([rk ]_ st'))))%asm_expr =
  heap.dom (heap_cut h (Z.abs_nat (u2Z ([rx ]_ st') / 4)) (Z.abs_nat (u2Z ([rk ]_ st'))))%asm_expr.
  case : Hnew => Hfit Hover Hmem.
  apply assert_m.mapstos_inv_dom in Hmem => //; last by rewrite size_Z2ints.
  rewrite size_Z2ints in Hmem.
  by rewrite -Hrx_invariant -Hrk Hmem /heap_cut /heap_mint.
by rewrite -Htmp' -(heap.dom_dom_proj h).
Qed.

Lemma dom_heap_mint_sign_state_invariant h h' nk rx st st' x s slen slen' :
  ([rx ]_ st = [rx ]_ st')%asm_expr ->
  (heap.get (Z.abs_nat (u2Z [rx]_ st / 4)) h = Some slen)%asm_expr ->
  (heap.get (Z.abs_nat (u2Z [rx]_ st' / 4)) h' = Some slen')%asm_expr ->
  (heap.get ((Z.abs_nat (u2Z ([rx]_ st `+ four32) / 4))) h =
   heap.get ((Z.abs_nat (u2Z ([rx]_ st' `+ four32) / 4))) h')%asm_expr ->
  var_mint x (signed nk rx) s st (heap_mint (signed nk rx) st h) ->
  heap.dom h = heap.dom h' ->
  heap.dom (heap_mint (signed nk rx) st h) = heap.dom (heap_mint (signed nk rx) st' h').
Proof.
move=> Hrx Hslen Hslen' Hptr Hvar_mint h_h'.
case: Hvar_mint => slen_ ptr A header_fit encoding payload_fit H.
case: H => h1 [h2 [Hdisj [Hunion [Hh1 Hh2]]]] /=.
have ? : slen = slen_.
  have X : heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)) (heap_mint (signed nk rx) st h) = Some slen_.
    rewrite Hunion.
    apply heap.get_union_L => //.
    rewrite /= in Hh1.
    case: Hh1 => h11 [h12 [h11_d_h12 [h11_U_h12 [Hh11 Hh12]]]].
    case: Hh11 => p [Hp Hh11].
    rewrite h11_U_h12.
    apply heap.get_union_L => //.
    by rewrite Hh11 Hp mulZC Z_div_mult_full // Zabs2Nat.id heap.get_sing.
  move/heap_get_heap_mint_inv : X.
  rewrite Hslen.
  by case.
subst slen_.
have H'slen : heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)) h = Some slen.
  have H'slen : heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)) h1 = Some slen.
    rewrite -(plus_0_r (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4))).
    rewrite -/(eval (var_e rx) st)%asm_expr.
    apply (assert_m.mapstos_get_inv 2 (slen :: ptr :: List.nil)%list) => //; by auto.
  apply heap_get_heap_mint_inv with st (signed nk rx).
  rewrite Hunion; by apply heap.get_union_L.
have H'ptr: heap.get (Z.abs_nat (u2Z ([rx ]_ st `+ four32 )%asm_expr / 4)) h = Some ptr.
  have H'ptr : heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4) + 1)%nat h1 = Some ptr.
    rewrite -/(eval (var_e rx) st)%asm_expr.
    apply (assert_m.mapstos_get_inv 2 (slen :: ptr :: List.nil)%list) => //; by auto.
  apply heap_get_heap_mint_inv with st (signed nk rx).
  rewrite u2Z_add_Z2u //.
  rewrite -{1}(Zmult_1_l 4) Z_div_plus_full // Zabs_nat_Zplus //; last first.
    by apply Z_div_pos => //; exact: min_u2Z.
  rewrite (_ : Z.abs_nat 1 = 1%nat) //.
  rewrite Hunion; exact: heap.get_union_L.
  rewrite -Zbeta1E; lia.
move: Hunion => /=.
rewrite H'slen Hslen' H'ptr.
move=> Hunion.
rewrite -Hptr H'ptr /heap_cut -heap.proj_app -heap.proj_app -Hrx.
by apply heap.dom_dom_proj.
Qed.

(* TODO: derive from the above *)
Lemma dom_heap_mint_signed_unchanged_state : forall h h' nk rx st st' x s,
  ([rx ]_ st = [rx ]_ st')%asm_expr ->
  (heap.get (Z.abs_nat (u2Z [rx]_ st / 4)) h = heap.get (Z.abs_nat (u2Z [rx]_ st' / 4)) h')%asm_expr ->
  (heap.get (Z.abs_nat (u2Z [rx]_ st / 4)).+1 h = heap.get (Z.abs_nat (u2Z [rx]_ st' / 4)).+1 h')%asm_expr ->
  var_mint x (signed nk rx) s st (heap_mint (signed nk rx) st h) ->
  heap.dom h = heap.dom h' ->
  heap.dom (heap_mint (signed nk rx) st h) = heap.dom (heap_mint (signed nk rx) st' h').
Proof.
move=> h h' nk rx st st' x s Hrx Hslen Hptr Hvar_mint h_h'.
case: Hvar_mint => slen ptr A header_fit encoding payload_fit H.
case: H => h1 [h2 [Hdisj [Hunion [Hh1 Hh2]]]] /=.
have H'slen : heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)) h = Some slen.
  have H'slen : heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)) h1 = Some slen.
    rewrite -(plus_0_r (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4))).
    rewrite -/(eval (var_e rx) st)%asm_expr.
    apply (assert_m.mapstos_get_inv 2 (slen :: ptr :: nil)) => //; by auto.
  apply heap_get_heap_mint_inv with st (signed nk rx).
  rewrite Hunion; by apply heap.get_union_L.
have H'ptr : heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)).+1 h = Some ptr.
  have H'ptr : heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4) + 1)%nat h1 = Some ptr.
    rewrite -/(eval (var_e rx) st)%asm_expr.
    apply (assert_m.mapstos_get_inv 2 (slen :: ptr :: nil)) => //; by auto.
  apply heap_get_heap_mint_inv with st (signed nk rx).
  rewrite addnC in H'ptr.
  rewrite Hunion; by apply heap.get_union_L.
move: Hunion => /=.
rewrite -Hslen H'slen u2Z_add_Z2u //; last by rewrite -Zbeta1E; lia.
rewrite -{1}(Zmult_1_l 4) Z_div_plus_full // Zabs_nat_Zplus //; last first.
  apply Z_div_pos => //; apply min_u2Z.
rewrite plus_comm (_ : Z.abs_nat 1 = 1%nat) //= H'ptr.
move=> Hunion.
rewrite u2Z_add_Z2u //; last by rewrite -Zbeta1E -Hrx; lia.
rewrite -{3}(Zmult_1_l 4) Z_div_plus_full // Zabs_nat_Zplus //; last first.
  apply Z_div_pos => //; apply min_u2Z.
rewrite plus_comm (_ : Z.abs_nat 1 = 1%nat) //= -Hptr H'ptr /heap_cut.
rewrite -2!heap.proj_app -Hrx; exact: heap.dom_dom_proj.
Qed.

Lemma heap_mint_unsign_state_invariant : forall d x s h h' rk rx st st',
  ([rk ]_ st = [rk ]_ st')%asm_expr ->
  ([rx ]_ st = [rx ]_ st')%asm_expr ->
  var_mint x (unsign rk rx) s st (heap_mint (unsign rk rx) st h) ->
  h \D\ heap.dom d = h' \D\ heap.dom d ->
  heap_mint (unsign rk rx) st h # d ->
  heap_mint (unsign rk rx) st h = heap_mint (unsign rk rx) st' h'.
Proof.
move=> d x s h h' rk rx st st' Hrk Hrx_invariant Hnew H_h_h' Hdisj.
have dom_h_t :
  (iota (Z.abs_nat (u2Z ([rx ]_ st) / 4)) (Z.abs_nat (u2Z ([rk ]_ st))))%asm_expr =
  heap.dom (heap_cut h (Z.abs_nat (u2Z ([rx ]_ st) / 4)) (Z.abs_nat (u2Z ([rk ]_ st))))%asm_expr.
  symmetry.
  by eapply var_mint_unsign_dom_heap_mint; eauto.
rewrite /= /heap_cut.
rewrite {1}(heap.proj_restrict (h \D\ heap.dom d)); last 2 first.
  by apply heap.inclu_difs.
  rewrite dom_h_t.
  apply heap.inclu_inc_dom, heap.disj_proj_inclu.
  rewrite /heap_mint in Hdisj.
  by rewrite dom_h_t heap.proj_dom_proj.
symmetry.
set l1 := iota _ _.
set l2 := iota _ _.
have -> : l1 = l2 by rewrite /l1 /l2 Hrk Hrx_invariant.
rewrite {1}(heap.proj_restrict (h' \D\ heap.dom d)); last 2 first.
  by apply heap.inclu_difs.
  rewrite /l2 dom_h_t -H_h_h'.
  apply heap.inclu_inc_dom, heap.disj_proj_inclu.
  rewrite /heap_mint in Hdisj.
  by rewrite dom_h_t heap.proj_dom_proj.
by rewrite H_h_h'.
Qed.

Lemma heap_mint_signed_state_invariant d x s h h' nk rx st st' :
  ([rx ]_ st = [rx ]_ st')%asm_expr ->
  var_mint x (signed nk rx) s st (heap_mint (signed nk rx) st h) ->
  h \D\ heap.dom d = h' \D\ heap.dom d ->
  heap_mint (signed nk rx) st h # d ->
  heap_mint (signed nk rx) st h = heap_mint (signed nk rx) st' h'.
Proof.
move=> rx_unchanged Hnew H_h_h' Hdisj /=.
rewrite -rx_unchanged.
case : Hnew => slen ptr A rx_fit encoding fit mem.
have H0 : heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)) h = Some slen.
  move: mem;  rewrite assert_m.conAE.
  move/con_heap_mint_signed_con_TT; by move/assert_m.mapsto_con_get.
rewrite H0.
have H1 : heap.get (Z.abs_nat (u2Z (([rx ]_ st)%asm_expr `+ four32) / 4)) h = Some ptr.
  move/con_heap_mint_signed_con_TT : mem => mem.
  rewrite /= in mem.
  rewrite assert_m.conAE assert_m.conCE assert_m.conAE assert_m.conAE in mem.
  by move/assert_m.mapsto_con_get : mem.
rewrite H1.
have H2 : heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)) h' =
  heap.get (Z.abs_nat (u2Z ([rx ]_ st)%asm_expr / 4)) h.
  set adr := Z.abs_nat _.
  have Htmp : adr \notin heap.dom d.
    rewrite /= H0 H1 heap.disjE in Hdisj.
    apply: seq_ext.dis_not_in; last by apply Hdisj.
    apply heap.in_dom_union_L, heap.in_dom_proj.
    - by rewrite mem_iota /adr leqnn andTb addn2.
    - eapply heap.get_Some_in_dom; by apply H0.
  transitivity (heap.get adr (h' \D\ heap.dom d)); by [rewrite heap.get_difs | rewrite -H_h_h' heap.get_difs].
rewrite H2 H0.
have H3 : heap.get (Z.abs_nat (u2Z (([rx ]_ st)%asm_expr `+ four32) / 4)) h' =
  heap.get (Z.abs_nat (u2Z (([rx ]_ st)%asm_expr `+ four32) / 4)) h.
  set adr := Z.abs_nat _.
  have Htmp : adr \notin heap.dom d.
    rewrite /= H0 H1 heap.disjE in Hdisj.
    apply: seq_ext.dis_not_in; last by apply Hdisj.
    apply heap.in_dom_union_L, heap.in_dom_proj; last first.
      eapply heap.get_Some_in_dom; by apply H1.
    rewrite mem_iota.
    rewrite /adr u2Z_add_Z2u //; last by rewrite -Zbeta1E; lia.
    rewrite {2}(_ : 4 = 1 * 4) // Z_div_plus_full // Zabs_nat_Zplus //; last first.
      apply Z_div_pos => //; by apply min_u2Z.
    by rewrite plusE addn1 addn2 ltnS leqnn andbT.
  transitivity (heap.get adr (h' \D\ heap.dom d)).
  - by rewrite heap.get_difs.
  - by rewrite -H_h_h' heap.get_difs.
rewrite H3 H1 /heap_cut.
set seq_rx_2 := {1 2}(iota _ _). set seq_ptr_slen := (iota _ _).
f_equal.
- have Htmp : seq_rx_2 = heap.dom (heap_cut h (Z.abs_nat (u2Z ([rx ]_ st) / 4)) 2)%asm_expr.
    rewrite /heap_cut heap.dom_proj_exact; [done| exact/ordset.ordered_iota |].
    move: mem; move/con_heap_mint_signed_con_TT.
    exact: assert_m.mapstos_inc_inv.
  rewrite {1}Htmp (heap.proj_restrict (h \D\ heap.dom d)); last 2 first.
    exact: heap.inclu_difs.
    apply heap.inclu_inc_dom, heap.disj_proj_inclu.
    rewrite /heap_mint H0 H1 /heap_cut in Hdisj.
    move/heap.disj_sym : Hdisj; case/heap.disj_union_inv; by move/heap.disj_sym.
  rewrite Htmp (heap.proj_restrict (h' \D\ heap.dom d) h'); last 2 first.
    exact: heap.inclu_difs.
    rewrite -H_h_h'.
    apply heap.inclu_inc_dom, heap.disj_proj_inclu.
    rewrite /heap_mint H0 H1 /heap_cut in Hdisj.
    move/heap.disj_sym : Hdisj; case/heap.disj_union_inv; by move/heap.disj_sym.
  by rewrite H_h_h'.
- have Htmp : seq_ptr_slen = heap.dom (heap_cut h (Z.abs_nat (u2Z ptr / 4)) nk).
    rewrite /heap_cut heap.dom_proj_exact; [done| exact/ordset.ordered_iota | ].
    move: mem.
    do 2 rewrite assert_m.conAE assert_m.conCE; rewrite assert_m.conAE.
    move/con_heap_mint_signed_con_TT.
    move/assert_m.mapstos_inc_inv.
    case: encoding => -> _ _ _.
    by apply.
  rewrite {1}Htmp (heap.proj_restrict (h \D\ heap.dom d)); last 2 first.
    by apply heap.inclu_difs.
    apply heap.inclu_inc_dom, heap.disj_proj_inclu.
    rewrite /heap_mint H0 H1 /heap_cut in Hdisj.
    move/heap.disj_sym : Hdisj; case/heap.disj_union_inv=> _; by move/heap.disj_sym.
  rewrite Htmp (heap.proj_restrict (h' \D\ heap.dom d) h'); last 2 first.
    by apply heap.inclu_difs.
    rewrite -H_h_h'.
    apply heap.inclu_inc_dom, heap.disj_proj_inclu.
    rewrite /heap_mint H0 H1 /heap_cut in Hdisj.
    move/heap.disj_sym : Hdisj; case/heap.disj_union_inv=> _; by move/heap.disj_sym.
  by rewrite -H_h_h'.
Qed.

Lemma heap_mint_state_invariant d x s h h' : forall tx st st',
  (forall x, List.In x (mint_regs tx) -> ([x ]_ st = [x ]_ st')%asm_expr) ->
  var_mint x tx s st (heap_mint tx st h) ->
  h \D\ heap.dom d = h'\D\ heap.dom d ->
  heap_mint tx st h # d ->
  heap_mint tx st h = heap_mint tx st' h'.
Proof.
move=> [rk rx|nk rx] st st' Hunchanged Hvar_mint Hdifs Hdisj.
- apply (heap_mint_unsign_state_invariant d x s) => //.
  by apply Hunchanged, mint_regs_unsigned1.
  by apply Hunchanged, mint_regs_unsigned2.
- apply (heap_mint_signed_state_invariant d x s) => //.
  apply Hunchanged; by rewrite /=; intuition.
Qed.

(** relation between a store of seplog variables and several mips multi_ints *)

Require order finmap.

Module Mint <: finmap.EQTYPE.

Definition A : eqType := mint_eqType.

End Mint.

Module assoc := finmap.map order.NatOrder Mint.

Notation "k '\U+' m" := (assoc.union k m) (at level 69) : assoc_scope.
Notation "a |=> b" := (assoc.sing a b) (at level 66) : assoc_scope.

Ltac assoc_get_Some :=
  match goal with
    | |- assoc.get ?x (assoc.union (assoc.sing ?x ?rx) ?d) = Some ?rk =>
      by apply assoc.get_union_sing_eq
    | |- assoc.get ?x (assoc.union (assoc.sing ?y ?ry) ?d) = Some ?rk =>
      rewrite assoc.get_union_sing_neq; [ assoc_get_Some | solve[ assumption | Uniq_neq] ]
    | |- assoc.get ?x (assoc.sing ?x ?rx) = Some ?rx =>
      apply assoc.get_sing
    | H : assoc.get ?x ?d = Some ?rx |- assoc.get ?x ?d = Some ?rx => exact H
  end.

Module assoc_prop_m := finmap.Map_Prop assoc.
Module assoc_tac_m := finmap.Map_Tac assoc.

Definition state_mint (d : assoc.t) : Rel := fun st s h =>
  (forall x mx, assoc.get x d = |_ mx _| ->
    var_mint x mx st s (heap_mint mx s h)) /\
  (forall x y, x <> y ->
    forall mx my, assoc.get x d = |_ mx _| -> assoc.get y d = |_ my _| ->
      heap_mint mx s h # heap_mint my s h)%asm_expr.

Local Open Scope assoc_scope.

Lemma state_mint_var_mint d s st h x rx : state_mint d s st h ->
  assoc.get x d = Some rx -> var_mint x rx s st (heap_mint rx st h)%asm_expr.
Proof. case=> H1 _ H; by apply H1. Qed.

Lemma state_mint_align rk x rx d s st h :
  state_mint (x |=> unsign rk rx \U+ d) s st h ->
  u2Z ([ rx ]_st)%asm_expr mod 4 = 0.
Proof.
move/state_mint_var_mint. move/(_ x (unsign rk rx)).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => _ _.
by move/assert_m.mapstos_inv_addr.
Qed.

Lemma state_mint_head_unsign_fit rk x rx d s st h :
  state_mint (x |=> unsign rk rx \U+ d) s st h ->
  (u2Z ([rx ]_ st)%asm_expr + 4 * Z_of_nat (Z.abs_nat (u2Z ([rk ]_ st))%asm_expr) < \B^1)%asm_expr.
Proof.
rewrite /state_mint.
case=> X _.
move: {X}(X x (unsign rk rx)) => X.
lapply X; last by rewrite assoc.get_union_sing_eq.
rewrite /var_mint.
case; tauto.
Qed.

Lemma state_mint_signed_fit_ptr L x rx d s st h ptr :
  state_mint (x |=> signed L rx \U+ d) s st h ->
  heap.get (Z.abs_nat (u2Z ([rx]_st `+ four32)%asm_expr / 4)) (heap_mint (signed L rx) st h) = Some ptr ->
  (u2Z ptr + 4 * Z_of_nat L < \B^1)%asm_expr.
Proof.
move=> s_st_h ptr_vx4.
move: (state_mint_var_mint _ _ _ _ x (signed L rx) s_st_h).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => slen_ ptr_ A _ encoding ptr_fit H.
move/assert_m.mapstos_get2 : H.
rewrite [u2Z _]/= ptr_vx4.
by case => ->.
Qed.

Lemma state_mint_signed_slen_L L x rx d s st h slen :
  state_mint (x |=> signed L rx \U+ d) s st h ->
  heap.get (Z.abs_nat (u2Z ([rx]_st)%asm_expr / 4)) (heap_mint (signed L rx) st h) = Some slen ->
  s2Z slen = sgZ (s2Z slen) * Z_of_nat L.
Proof.
move=> s_st_h ptr_vx.
move: (state_mint_var_mint _ _ _ _ x (signed L rx) s_st_h).
rewrite assoc.get_union_sing_eq.
case/(_ (refl_equal _)) => slen_ ptr_ A _ encoding ptr_fit H.
move/assert_m.mapstos_get1 : H.
rewrite [u2Z _]/= ptr_vx.
case => ->.
by case: encoding.
Qed.

Ltac Var_unchanged :=
  match goal with
    | Hid : (Some (?s1, ?h1) -- ?c ---> Some (?s2, ?h2))%pseudo_cmd
      |- ( [ ?x ]_ ?s1 = [ ?x ]_ ?s2 )%pseudo_expr =>
        apply syntax_m.var_unchanged with h1 c h2; [exact Hid | idtac]
  end.

(** for any s' such [ v ]_s' is in the goal,
    rewrite [ v ]_s' with [ v ]_s if [ v ]_s = [ v ]_s' is provable *)

Ltac Rewrite_var v st :=
  match goal with
    | |- context [syntax_m.seplog_m.assert_m.expr_m.store.get v ?st'] =>
      rewrite (_ : syntax_m.seplog_m.assert_m.expr_m.store.get v st' =
        syntax_m.seplog_m.assert_m.expr_m.store.get v st);
        [ idtac |
          symmetry;
          Var_unchanged ;
          rewrite [syntax_m.seplog_m.modified_vars _]/= ;
          move/seq_ext.inP ;
          rewrite -/(~ _) ;
          now Uniq_not_In ]
  end.

Ltac Rewrite_reg rk st :=
  match goal with
    |- context [store.get ?rk ?st'] =>
      rewrite (_ : store.get rk st' = store.get rk st) ;
        [ idtac |
          symmetry ;
          mips_syntax.Reg_unchanged ;
          simpl mips_frame.modified_regs ;
          now Uniq_not_In ]
  end.

Lemma state_mint_invariant : forall d c, ~~ mips_syntax.contains_sw c ->
  disj (mips_frame.modified_regs c) (mints_regs (assoc.cdom d)) ->
  invariant (fun s st h => state_mint d s st h) c.
Proof.
move=> d c Hnosw Hinter.
rewrite /invariant => s st he Hs_st_he st' h' Hexec.
rewrite /state_mint; split.
- move=> x rx H_rx_x.
  move: {Hs_st_he}(proj1 Hs_st_he x rx H_rx_x) => Hs_st_he.
  move: Hs_st_he.
  have -> : he = h' by eapply mips_syntax.no_sw_heap_invariant; eauto.
  have X : forall rx0 : reg_eqType,
   List.In rx0 (mint_regs rx) -> ([rx0 ]_ st)%asm_expr = ([rx0 ]_ st')%asm_expr.
      move=> rx0 Hrx0.
      Reg_unchanged.
      apply/(disj_not_In Hinter)/(In_mints_regs _ _ rx) => //.
      apply/inP; by move/assoc.get_Some_in_cdom : H_rx_x.
  rewrite (heap_mint_store_invariant st') //.
  exact: var_mint_invariant.
- move=> x y Hxy rx ry H_rx_x H_ry_y.
  move: {Hs_st_he}(proj2 Hs_st_he _ _ Hxy _ _ H_rx_x H_ry_y) => Hs_st_he.
  have X : forall x0 : reg_eqType,
    List.In x0 (mint_regs rx) -> ([x0 ]_ st')%asm_expr = ([x0 ]_ st)%asm_expr.
    move=> x0 Hx0.
    symmetry.
    Reg_unchanged.
    apply/(disj_not_In Hinter)/(In_mints_regs _ _ rx) => //.
    apply/inP; by apply assoc.get_Some_in_cdom in H_rx_x.
  have Y : forall x0 : reg_eqType,
    List.In x0 (mint_regs ry) -> ([x0 ]_ st')%asm_expr = ([x0 ]_ st)%asm_expr.
    move=> x0 Hx0.
    symmetry.
    Reg_unchanged.
    apply/(disj_not_In Hinter)/(In_mints_regs _ _ ry) => //.
    apply/inP; by apply assoc.get_Some_in_cdom in H_ry_y.
  rewrite (heap_mint_store_invariant st) // (heap_mint_store_invariant st st') //.
  suff : he = h' by move=> <-.
  by eapply mips_syntax.no_sw_heap_invariant; eauto.
Qed.

Lemma state_mint_store_upd d s st h rx vx :
  rx \notin (mints_regs (assoc.cdom d)) ->
  state_mint d s st h -> state_mint d s (store.upd rx vx st) h.
Proof.
move=> Hrx H.
rewrite /state_mint; split.
  move=> y my y_my.
  apply var_mint_invariant with s st => //.
    move=> ry Hry.
    rewrite store.get_upd //.
    move=> abs; subst ry.
    move/negP : Hrx; apply.
    apply/seq_ext.inP.
    apply In_mints_regs with my => //.
    apply/seq_ext.inP.
    by apply assoc.get_Some_in_cdom with y.
  move: (proj1 H _ _ y_my).
  suff : heap_mint my (store.upd rx vx st) h = heap_mint my st h by move=> ->.
  apply heap_mint_store_invariant => ry Hry.
    (* copipe *)
    rewrite store.get_upd //.
    move=> abs; subst ry.
    move/negP : Hrx; apply.
    apply/seq_ext.inP.
    apply In_mints_regs with my => //.
    apply/seq_ext.inP.
    by apply assoc.get_Some_in_cdom with y.
    (* copipe *)
move=> x y x_y mx my x_mx y_my.

rewrite (heap_mint_store_invariant st); last first.
    move=> ry Hry.
    rewrite store.get_upd //.
    move=> abs; subst ry.
    move/negP : Hrx; apply.
    apply/seq_ext.inP.
    apply In_mints_regs with mx => //.
    apply/seq_ext.inP.
    by apply assoc.get_Some_in_cdom with x.
rewrite (heap_mint_store_invariant st); last first.
    move=> ry Hry.
    rewrite store.get_upd //.
    move=> abs; subst ry.
    move/negP : Hrx; apply.
    apply/seq_ext.inP.
    apply In_mints_regs with my => //.
    apply/seq_ext.inP.
    by apply assoc.get_Some_in_cdom with y.
by apply (proj2 H) with x y.
Qed.

Lemma state_mint_part2_one_variable x mA d h h' st st' s :
  state_mint (x |=> mA \U+ d) s st h ->
  heap.dom (heap_mint mA st' h') = heap.dom (heap_mint mA st h) ->
  (forall t x0,
    t \in assoc.cdom (x |=> mA \U+ d) ->
    List.In x0 (mint_regs t) ->
    ([x0 ]_ st)%asm_expr = ([x0 ]_ st')%asm_expr) ->
  h \D\ heap.dom (heap_mint (mA) st h) =
  h' \D\ heap.dom (heap_mint (mA) st h) ->
  heap.dom h = heap.dom h' ->
  forall x0 y : assoc.l,
    x0 <> y ->
    forall rx0 ry : assoc.v,
      assoc.get x0 (x |=> mA \U+ d) = Some rx0 ->
      assoc.get y (x |=> mA \U+ d) = Some ry ->
      heap_mint rx0 st' h' # heap_mint ry st' h'.
Proof.
move=> s_st_h Hdom H1 H2 H3.
- move=> y z y_z ry rz Hry Hrz.
  move: (proj2 s_st_h _ _ y_z _ _ Hry Hrz).
  case/orP : (orbN (z == x)); [move/eqP => z_x; subst z | move/eqP => z_x].
  + rewrite assoc.get_union_sing_eq // in Hrz. case: Hrz => ?; subst rz.
    rewrite assoc.get_union_sing_neq // in Hry.
    have <- : heap_mint ry st h = heap_mint ry st' h'.
      apply (heap_mint_state_invariant (heap_mint mA st h) y s).
      * move=> x0 Hx0.
        apply H1 with ry => //.
        apply assoc.get_Some_in_cdom with y.
        by rewrite assoc.get_union_sing_neq.
      * apply (proj1 s_st_h); by rewrite assoc.get_union_sing_neq.
      * exact H2.
      * apply (proj2 s_st_h _ _ y_z); by [rewrite assoc.get_union_sing_neq | rewrite assoc.get_union_sing_eq].
    move=> H.
    eapply heap.disj_same_dom; first by apply H.
    by [].
  + have : heap_mint rz st h = heap_mint rz st' h'.
      apply (heap_mint_state_invariant (heap_mint mA st h) z s).
      * move=> x0 Hx0.
        apply H1 with rz => //.
        by apply assoc.get_Some_in_cdom with z.
      * by apply (proj1 s_st_h _ _ Hrz).
      * exact H2.
      * apply (proj2 s_st_h _ _ z_x) => //; by rewrite assoc.get_union_sing_eq.
    move=> ->.
    case/orP : (orbN (y == x)); [move/eqP => y_x; subst y | move/eqP => y_x].
    * rewrite assoc.get_union_sing_eq in Hry; case: Hry => ?; subst ry.
      rewrite assoc.get_union_sing_neq in Hrz; last by auto.
      move/heap.disj_sym => H.
      apply heap.disj_sym.
      eapply heap.disj_same_dom; first by apply H.
      symmetry.
      by [].
    * suff : heap_mint ry st h = heap_mint ry st' h' by move=> ->.
      apply (heap_mint_state_invariant (heap_mint mA st h) y s).
      - move=> x0 Hx0.
        apply H1 with ry => //.
        by apply assoc.get_Some_in_cdom with y.
      - by apply (proj1 s_st_h _ _ Hry).
      - exact H2.
      - apply (proj2 s_st_h _ _ y_x) => //; by rewrite assoc.get_union_sing_eq.
Qed.

Lemma state_mint_part2_one_variable_unsign x rk rx d h h' st st' s :
  state_mint (x |=> unsign rk rx \U+ d) s st h ->
  (forall t x0,
    t \in assoc.cdom (x |=> unsign rk rx \U+ d) ->
    List.In x0 (mint_regs t) ->
    ([x0 ]_ st)%asm_expr = ([x0 ]_ st')%asm_expr) ->
  h \D\ heap.dom (heap_mint (unsign rk rx) st h) =
  h' \D\ heap.dom (heap_mint (unsign rk rx) st h) ->
  heap.dom h = heap.dom h' ->
  forall x0 y : assoc.l,
    x0 <> y ->
    forall rx0 ry : assoc.v,
      assoc.get x0 (x |=> unsign rk rx \U+ d) = Some rx0 ->
      assoc.get y (x |=> unsign rk rx \U+ d) = Some ry ->
      heap_mint rx0 st' h' # heap_mint ry st' h'.
Proof.
move=> s_st_h H1 H2 H3.
eapply state_mint_part2_one_variable.
- by apply s_st_h.
- symmetry.
  apply dom_heap_mint_unsign_state_invariant with x s => //.
  + apply H1 with (unsign rk rx).
    * apply assoc.get_Some_in_cdom with x.
      by rewrite assoc.get_union_sing_eq.
    * by apply mint_regs_unsigned1.
  + apply H1 with (unsign rk rx).
    * apply assoc.get_Some_in_cdom with x.
      by rewrite assoc.get_union_sing_eq.
    * by apply mint_regs_unsigned2.
  + eapply state_mint_var_mint; first by apply s_st_h.
    by rewrite assoc.get_union_sing_eq.
- exact H1.
- exact H2.
- exact H3.
Qed.

Lemma state_mint_part2_two_variables A y mA my d s st h st' h' :
  heap.dom (heap_mint mA st' h') = heap.dom (heap_mint mA st h) ->
  heap.dom (heap_mint my st' h') = heap.dom (heap_mint my st h) ->
  state_mint (A |=> mA \U+ (y |=> my \U+ d)) s st h ->
  (forall t,
    t \in assoc.cdom (A |=> mA \U+ (y |=> my \U+ d)) ->
    forall x0, List.In x0 (mint_regs t) -> [x0 ]_ st = [x0 ]_ st')%asm_expr ->
  A \notin assoc.dom d -> y \notin assoc.dom d ->
  A <> y ->
  h \D\ heap.dom (heap_mint my st h \U heap_mint mA st h) =
  h' \D\ heap.dom (heap_mint my st h \U heap_mint mA st h) ->
  forall x y0, x <> y0 -> forall rx ry0,
   assoc.get x (A |=> mA \U+ (y |=> my \U+ d)) = Some rx ->
   assoc.get y0 (A |=> mA \U+ (y |=> my \U+ d)) = Some ry0 ->
   heap_mint rx st' h' # heap_mint ry0 st' h'.
Proof.
move=> dom_rA dom_rx s_st_h H1 A_d y_d A_y H2 x y0 x_y0 rx ry0 Hrx Hry0.
case/assoc.get_union_Some_inv : Hrx => Hrx.
+ (* x = A *) case/assoc.get_sing_inv : Hrx => ? ?; subst x rx.
  rewrite heap.disjE dom_rA -heap.disjE.
  case/assoc.get_union_Some_inv : Hry0 => Hry0.
  * case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
    by move: (x_y0 (refl_equal _)).
  * case/assoc.get_union_Some_inv : Hry0 => Hry0.
    - case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
      rewrite heap.disjE dom_rx -heap.disjE.
      apply (proj2 s_st_h A y) => //.
      by assoc_get_Some.
      rewrite assoc.get_union_sing_neq; last by apply not_eq_sym.
      by rewrite assoc.get_union_sing_eq.
    - have <- : heap_mint ry0 st h = heap_mint ry0 st' h'.
        apply (heap_mint_state_invariant (heap_mint my st h \U heap_mint mA st h) y0 s).
        + apply H1.
          apply assoc.get_Some_in_cdom with y0.
          rewrite assoc.get_union_sing_neq; last by auto.
          apply assoc.get_union_R => //.
          rewrite assoc.disjE assoc.dom_sing /=.
          by rewrite (negbTE y_d).
        + eapply state_mint_var_mint; first by apply s_st_h.
          rewrite assoc.get_union_sing_neq; last by auto.
          apply assoc.get_union_R => //.
          rewrite assoc.disjE assoc.dom_sing /=.
          by rewrite (negbTE y_d).
        + exact H2.
        + apply heap.disjhU.
          * apply (proj2 s_st_h y0 y).
            * move=> ?; subst y0.
              move/assoc.get_Some_in_dom : Hry0.
              by apply/negPn.
            * rewrite assoc.unionA.
              apply assoc.get_union_R; last by exact Hry0.
              apply assoc.disjUh.
              by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
              by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
            * rewrite assoc.get_union_sing_neq; last by apply not_eq_sym.
              by rewrite assoc.get_union_sing_eq.
          * apply (proj2 s_st_h y0 A).
            * by apply not_eq_sym.
            * rewrite assoc.unionA.
              apply assoc.get_union_R; last by exact Hry0.
              apply assoc.disjUh.
              by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
              by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
            * by assoc_get_Some.
      apply (proj2 s_st_h A y0) => //.
      - by rewrite assoc.get_union_sing_eq.
      - rewrite assoc.unionA.
        apply assoc.get_union_R; last by exact Hry0.
        apply assoc.disjUh.
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
        by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
+ (* x = y or y \in d *) case/assoc.get_union_Some_inv : Hrx => Hrx.
  * case/assoc.get_sing_inv : Hrx => ? ?; subst x rx.
    rewrite heap.disjE dom_rx -heap.disjE.
    case/assoc.get_union_Some_inv : Hry0 => Hry0.
    + case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
      rewrite heap.disjE dom_rA -heap.disjE.
      apply (proj2 s_st_h y A) => //.
      rewrite assoc.get_union_sing_neq; last by auto.
      by rewrite assoc.get_union_sing_eq.
      by rewrite assoc.get_union_sing_eq.
    + rewrite assoc.get_union_sing_neq in Hry0; last by apply not_eq_sym.
      have y0_ry0 : assoc.get y0 (y |=> my \U+ (A |=> mA \U+ d)) = Some ry0.
        rewrite assoc.get_union_sing_neq; last by apply not_eq_sym.
        rewrite assoc.get_union_sing_neq //.
        move=> ?; subst y0.
        move/assoc.get_Some_in_dom : Hry0.
        by apply/negPn.
      have <- : heap_mint ry0 st h = heap_mint ry0 st' h'.
        apply heap_mint_state_invariant with (d := heap_mint my st h \U heap_mint mA st h) (x := y0) (s := s).
        * apply H1.
          apply assoc.get_Some_in_cdom with y0.
          rewrite assoc.unionA.
          apply assoc.get_union_R => //.
          apply assoc.disjUh.
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
        * eapply state_mint_var_mint; first by apply s_st_h.
          rewrite assoc.unionA.
          apply assoc.get_union_R => //.
          apply assoc.disjUh.
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
        * exact H2.
        * apply heap.disjhU.
          + apply (proj2 s_st_h y0 y); first by apply not_eq_sym.
            rewrite assoc.unionA.
            apply assoc.get_union_R; last by exact Hry0.
            apply assoc.disjUh.
            by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
            by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
            rewrite assoc.get_union_sing_neq; last by apply not_eq_sym.
            by rewrite assoc.get_union_sing_eq.
          + apply (proj2 s_st_h y0 A).
            * move=> ?; subst y0.
              move/assoc.get_Some_in_dom : Hry0.
              by apply/negPn.
            * rewrite assoc.unionA.
              apply assoc.get_union_R; last by exact Hry0.
              apply assoc.disjUh.
              by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
              by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
            * by assoc_get_Some.
      apply (proj2 s_st_h y y0).
      - exact x_y0.
      - rewrite assoc.get_union_sing_neq; last by apply not_eq_sym.
        by rewrite assoc.get_union_sing_eq.
      - rewrite assoc.unionA.
        apply assoc.get_union_R; last by exact Hry0.
        apply assoc.disjUh.
        by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
        by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
  * have <- : heap_mint rx st h = heap_mint rx st' h'.
      apply (heap_mint_state_invariant (heap_mint my st h \U heap_mint mA st h) x s).
      - apply H1.
        apply assoc.get_Some_in_cdom with x.
        apply assoc.get_union_R.
          apply assoc.disjhU.
            move/eqP in A_y; by apply assoc.disj_sing.
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
        apply assoc.get_union_R => //.
        by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
      - apply (state_mint_var_mint _ _ _ _ _ _ s_st_h).
        rewrite assoc.unionA.
        apply assoc.get_union_R; last by exact Hrx.
        apply assoc.disjUh.
        by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
        by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
      - exact H2.
      - apply heap.disjhU.
        + apply (proj2 s_st_h x y).
          * move=> ?; subst x.
            move/assoc.get_Some_in_dom : Hrx.
            by apply/negPn.
          * rewrite assoc.unionA.
            apply assoc.get_union_R; last by exact Hrx.
            apply assoc.disjUh.
            by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
            by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
          * rewrite assoc.get_union_sing_neq; last by auto.
            by rewrite assoc.get_union_sing_eq.
        + apply (proj2 s_st_h x A).
          * move=> ?; subst x.
            move/assoc.get_Some_in_dom : Hrx.
            by apply/negPn.
          * rewrite assoc.unionA.
            apply assoc.get_union_R; last by exact Hrx.
            apply assoc.disjUh.
            by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
            by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
          * by assoc_get_Some.
    case/assoc.get_union_Some_inv : Hry0 => Hry0.
    - case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
      rewrite heap.disjE dom_rA -heap.disjE.
      apply (proj2 s_st_h x A).
      + exact x_y0.
      + rewrite assoc.unionA.
        apply assoc.get_union_R; last by exact Hrx.
        apply assoc.disjUh.
        by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
        by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
      + by assoc_get_Some.
    - case/assoc.get_union_Some_inv : Hry0 => Hry0.
      + case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
        rewrite heap.disjE dom_rx -heap.disjE.
        apply (proj2 s_st_h x y).
        * exact x_y0.
        * rewrite assoc.unionA.
          apply assoc.get_union_R; last by exact Hrx.
          apply assoc.disjUh.
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
        * rewrite assoc.get_union_sing_neq; last by auto.
          by rewrite assoc.get_union_sing_eq.
      + have <- : heap_mint ry0 st h = heap_mint ry0 st' h'.
          apply (heap_mint_state_invariant (heap_mint my st h \U heap_mint mA st h) y0 s).
          - apply H1.
            apply assoc.get_Some_in_cdom with y0.
            apply assoc.get_union_R.
              apply assoc.disjhU.
                move/eqP in A_y; by apply assoc.disj_sing.
              by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
            apply assoc.get_union_R => //.
            by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
          - apply (state_mint_var_mint _ _ _ _ _ _ s_st_h).
            rewrite assoc.unionA.
            apply assoc.get_union_R; last by exact Hry0.
            apply assoc.disjUh.
            by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
            by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
          - exact H2.
          - apply heap.disjhU.
            + apply (proj2 s_st_h y0 y).
              * move=> ?; subst y0.
                move/assoc.get_Some_in_dom : Hry0.
                by apply/negPn.
              * rewrite assoc.unionA.
                apply assoc.get_union_R; last by exact Hry0.
                apply assoc.disjUh.
                by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
                by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
              * rewrite assoc.get_union_sing_neq; last by apply not_eq_sym.
                by rewrite assoc.get_union_sing_eq.
            + apply (proj2 s_st_h y0 A).
              * move=> ?; subst y0.
                move/assoc.get_Some_in_dom : Hry0.
                by apply/negPn.
              * rewrite assoc.unionA.
                apply assoc.get_union_R; last by exact Hry0.
                apply assoc.disjUh.
                by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
                by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
              * by assoc_get_Some.
        apply (proj2 s_st_h x y0).
        + exact x_y0.
        + rewrite assoc.unionA.
          apply assoc.get_union_R; last by exact Hrx.
          apply assoc.disjUh.
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
        + rewrite assoc.unionA.
          apply assoc.get_union_R; last by exact Hry0.
          apply assoc.disjUh.
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE A_d).
          by rewrite assoc.disjE assoc.dom_sing /= (negbTE y_d).
Qed.

Local Open Scope uniq_scope.

Lemma state_mint_part2_three_variables A y z mA my mz d s st h st' h' :
  heap.dom (heap_mint mA st' h') = heap.dom (heap_mint mA st h) ->
  heap.dom (heap_mint my st' h') = heap.dom (heap_mint my st h) ->
  heap.dom (heap_mint mz st' h') = heap.dom (heap_mint mz st h) ->
  state_mint (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) s st h ->
  (forall t,
    t \in assoc.cdom (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) ->
    forall x0, List.In x0 (mint_regs t) -> [x0 ]_ st = [x0 ]_ st')%asm_expr ->
  A \notin assoc.dom d -> y \notin assoc.dom d -> z \notin assoc.dom d ->
  uniq(A, y, z) ->
  h \D\ heap.dom (heap_mint mA st h \U heap_mint my st h \U heap_mint mz st h) =
  h' \D\ heap.dom (heap_mint mA st h \U heap_mint my st h \U heap_mint mz st h) ->
  forall x y0, x <> y0 -> forall rx ry0,
   assoc.get x (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) = Some rx ->
   assoc.get y0 (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) = Some ry0 ->
   heap_mint rx st' h' # heap_mint ry0 st' h'.
Proof.
move=> dom_rA dom_ry dom_rz s_st_h H1 A_d y_d z_d A_y_z H2 x y0 x_y0 rx ry0 Hrx Hry0.
case/assoc.get_union_Some_inv : Hrx => Hrx.
  (* x = A *)
  case/assoc.get_sing_inv : Hrx => ? ?; subst x rx.
  case/assoc.get_union_Some_inv : Hry0 => Hry0.
    (* x = A, y0 = A *)
    case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
      exfalso. by apply x_y0.
    (* x = A, y0 <> A *)
    case/assoc.get_union_Some_inv : Hry0 => Hry0.
      (* x = A, y0 = y *)
      case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
        rewrite heap.disjE dom_rA dom_ry -heap.disjE.
        apply (proj2 s_st_h A y) => //.
        by rewrite assoc.get_union_sing_eq.
        by assoc_get_Some.
      (* x = A, y0 <> y *)
      case/assoc.get_union_Some_inv : Hry0 => Hry0.
        (* x = A, y0 = z *)
        case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
          rewrite heap.disjE dom_rA dom_rz -heap.disjE.
          apply (proj2 s_st_h A z) => //.
          by rewrite assoc.get_union_sing_eq.
          by assoc_get_Some.
        rewrite heap.disjE dom_rA -heap.disjE.
        suff : heap_mint ry0 st h = heap_mint ry0 st' h'.
          move=> <-.
          apply (proj2 s_st_h A y0) => //.
          by rewrite assoc.get_union_sing_eq.
          rewrite assoc.get_union_sing_neq; last by auto.
          rewrite assoc.get_union_sing_neq; last first.
            move=> ?; subst y0.
            apply assoc.get_Some_in_dom in Hry0.
            by rewrite Hry0 in y_d.
          rewrite assoc.get_union_sing_neq //.
          move=> ?; subst y0.
          apply assoc.get_Some_in_dom in Hry0.
          by rewrite Hry0 in z_d.
        have Htmp : assoc.get y0 (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) = Some ry0.
          rewrite assoc.get_union_sing_neq; last by auto.
          rewrite assoc.get_union_sing_neq; last first.
            move=> ?; subst y0.
            apply assoc.get_Some_in_dom in Hry0.
            by rewrite Hry0 in y_d.
          rewrite assoc.get_union_sing_neq //.
          move=> ?; subst y0.
          apply assoc.get_Some_in_dom in Hry0.
          by rewrite Hry0 in z_d.
        apply (heap_mint_state_invariant (heap_mint mA st h \U
          heap_mint my st h \U heap_mint mz st h) y0 s) => //.
        - move=> x Hx.
          apply H1 with ry0 => //.
          by apply assoc.get_Some_in_cdom with y0.
        - by apply (proj1 s_st_h y0).
        - apply heap.disjhU.
          + apply heap.disjhU.
            * apply (proj2 s_st_h y0 A) => //.
              move=> ?; subst y0.
              apply assoc.get_Some_in_dom in Hry0.
              by rewrite Hry0 in A_d.
              by assoc_get_Some.
            * apply (proj2 s_st_h y0 y) => //.
              move=> ?; subst y0.
              apply assoc.get_Some_in_dom in Hry0.
              by rewrite Hry0 in y_d.
              by assoc_get_Some.
          + apply (proj2 s_st_h y0 z) => //.
            move=> ?; subst y0.
            apply assoc.get_Some_in_dom in Hry0.
            by rewrite Hry0 in z_d.
            by assoc_get_Some.
case/assoc.get_union_Some_inv : Hry0 => Hry0.
  case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
    case/assoc.get_union_Some_inv : Hrx => Hrx.
      case/assoc.get_sing_inv : Hrx => ? ?; subst x rx.
      rewrite heap.disjE dom_rA dom_ry -heap.disjE.
      apply (proj2 s_st_h y A) => //.
      by assoc_get_Some.
      by rewrite assoc.get_union_sing_eq.
    case/assoc.get_union_Some_inv : Hrx => Hrx.
      case/assoc.get_sing_inv : Hrx => ? ?; subst x rx.
      rewrite heap.disjE dom_rA dom_rz -heap.disjE.
      apply (proj2 s_st_h z A) => //.
      by assoc_get_Some.
      by rewrite assoc.get_union_sing_eq.
        rewrite heap.disjE dom_rA -heap.disjE.
        suff : heap_mint rx st h = heap_mint rx st' h'.
          move=> <-.
          apply (proj2 s_st_h x A) => //.
          rewrite assoc.get_union_sing_neq; last by auto.
          rewrite assoc.get_union_sing_neq; last first.
            move=> ?; subst x.
            apply assoc.get_Some_in_dom in Hrx.
            by rewrite Hrx in y_d.
          rewrite assoc.get_union_sing_neq //.
          move=> ?; subst x.
          apply assoc.get_Some_in_dom in Hrx.
          by rewrite Hrx in z_d.
          by rewrite assoc.get_union_sing_eq.
        have Htmp : assoc.get x (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) = Some rx.
          rewrite assoc.get_union_sing_neq //.
          rewrite assoc.get_union_sing_neq; last first.
            move=> ?; subst y.
            apply assoc.get_Some_in_dom in Hrx.
            by rewrite Hrx in y_d.
          rewrite assoc.get_union_sing_neq //.
          move=> ?; subst z.
          apply assoc.get_Some_in_dom in Hrx.
          by rewrite Hrx in z_d.
        apply (heap_mint_state_invariant (heap_mint mA st h \U
          heap_mint my st h \U heap_mint mz st h) x s) => //.
        - move=> x0 Hx0.
          apply H1 with rx => //.
          by apply assoc.get_Some_in_cdom with x.
        - by apply (proj1 s_st_h x).
        - apply heap.disjhU.
          + apply heap.disjhU.
            * apply (proj2 s_st_h x A) => //.
              by assoc_get_Some.
            * apply (proj2 s_st_h x y) => //.
              move=> ?; subst x.
              apply assoc.get_Some_in_dom in Hrx.
              by rewrite Hrx in y_d.
              by assoc_get_Some.
          + apply (proj2 s_st_h x z) => //.
            move=> ?; subst x.
            apply assoc.get_Some_in_dom in Hrx.
            by rewrite Hrx in z_d.
            by assoc_get_Some.
case/assoc.get_union_Some_inv : Hrx => Hrx.
  case/assoc.get_sing_inv : Hrx => ? ?; subst y my.
    case/assoc.get_union_Some_inv : Hry0 => Hry0.
      case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
        tauto.
      case/assoc.get_union_Some_inv : Hry0 => Hry0.
        case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.

      rewrite heap.disjE dom_rz dom_ry -heap.disjE.
      apply (proj2 s_st_h x z) => //.
      by assoc_get_Some.
      by assoc_get_Some.
      rewrite heap.disjE dom_ry -heap.disjE.
      suff : heap_mint ry0 st h = heap_mint ry0 st' h'.
        move=> <-.
        apply (proj2 s_st_h x y0) => //.
        by assoc_get_Some.
        rewrite assoc.get_union_sing_neq; last first.
          move=> ?; subst y0.
          apply assoc.get_Some_in_dom in Hry0.
          by rewrite Hry0 in A_d.
        rewrite assoc.get_union_sing_neq; last first.
          move=> ?; subst y0.
          apply assoc.get_Some_in_dom in Hry0.
          by rewrite Hry0 in y_d.
        rewrite assoc.get_union_sing_neq //.
        move=> ?; subst y0.
        apply assoc.get_Some_in_dom in Hry0.
        by rewrite Hry0 in z_d.
      have Htmp : assoc.get y0 (A |=> mA \U+ (x |=> rx \U+ (z |=> mz \U+ d))) = Some ry0.
        rewrite assoc.get_union_sing_neq; last first.
          move=> ?; subst y0.
          apply assoc.get_Some_in_dom in Hry0.
          by rewrite Hry0 in A_d.
        rewrite assoc.get_union_sing_neq; last first.
          move=> ?; subst y0.
          apply assoc.get_Some_in_dom in Hry0.
          by rewrite Hry0 in y_d.
        rewrite assoc.get_union_sing_neq //.
        move=> ?; subst y0.
        apply assoc.get_Some_in_dom in Hry0.
        by rewrite Hry0 in z_d.
      apply (heap_mint_state_invariant (heap_mint mA st h \U
        heap_mint rx st h \U heap_mint mz st h) y0 s) => //.
        move=> x0 Hx0.
        apply H1 with ry0 => //.
        apply assoc.get_Some_in_cdom with y0 => //.
        by apply (proj1 s_st_h).
        apply heap.disjhU.
        - apply heap.disjhU.
          + apply (proj2 s_st_h y0 A) => //.
              move=> ?; subst y0.
              apply assoc.get_Some_in_dom in Hry0.
              by rewrite Hry0 in A_d.
              by assoc_get_Some.
            * apply (proj2 s_st_h y0 x) => //.
              move=> ?; subst x.
              apply assoc.get_Some_in_dom in Hry0.
              by rewrite Hry0 in y_d.
              by assoc_get_Some.
          + apply (proj2 s_st_h y0 z) => //.
            move=> ?; subst y0.
            apply assoc.get_Some_in_dom in Hry0.
            by rewrite Hry0 in z_d.
            by assoc_get_Some.
case/assoc.get_union_Some_inv : Hrx => Hrx.
  case/assoc.get_sing_inv : Hrx => ? ?; subst x rx.
    case/assoc.get_union_Some_inv : Hry0 => Hry0.
      case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
        rewrite heap.disjE dom_rz dom_ry -heap.disjE.
        apply (proj2 s_st_h z y) => //.
        by assoc_get_Some.
        by assoc_get_Some.
    case/assoc.get_union_Some_inv : Hry0 => Hry0.
      case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
      tauto.
  rewrite heap.disjE dom_rz -heap.disjE.
  have Htmp : assoc.get y0 (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) = Some ry0.
    rewrite assoc.get_union_sing_neq; last first.
      move=> ?; subst y0.
      apply assoc.get_Some_in_dom in Hry0.
      by rewrite Hry0 in A_d.
    rewrite assoc.get_union_sing_neq; last first.
      move=> ?; subst y0.
      apply assoc.get_Some_in_dom in Hry0.
      by rewrite Hry0 in y_d.
    rewrite assoc.get_union_sing_neq //.
    move=> ?; subst y0.
    apply assoc.get_Some_in_dom in Hry0.
    by rewrite Hry0 in z_d.
  suff <- : heap_mint ry0 st h = heap_mint ry0 st' h'.
    apply (proj2 s_st_h z y0) => //.
    by assoc_get_Some.
  apply (heap_mint_state_invariant (heap_mint mA st h \U
    heap_mint my st h \U heap_mint mz st h) y0 s) => //.
  - move=> x Hx; apply H1 with ry0 => //.
    by apply assoc.get_Some_in_cdom with y0.
  - by apply (proj1 s_st_h).
  - apply heap.disjhU.
    + apply heap.disjhU.
      * apply (proj2 s_st_h y0 A) => //.
        move=> ?; subst y0.
        apply assoc.get_Some_in_dom in Hry0.
        by rewrite Hry0 in A_d.
        by assoc_get_Some.
      * apply (proj2 s_st_h y0 y) => //.
        - move=> ?; subst y0.
          apply assoc.get_Some_in_dom in Hry0.
          by rewrite Hry0 in y_d.
        - by assoc_get_Some.
    + apply (proj2 s_st_h y0 z) => //.
      * move=> ?; subst y0.
        apply assoc.get_Some_in_dom in Hry0.
        by rewrite Hry0 in z_d.
      * by assoc_get_Some.
case/assoc.get_union_Some_inv : Hry0 => Hry0.
  case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
    rewrite heap.disjE dom_ry -heap.disjE.
    have Htmp : assoc.get x (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) = Some rx.
      rewrite assoc.get_union_sing_neq; last first.
        move=> ?; subst x.
        apply assoc.get_Some_in_dom in Hrx.
        by rewrite Hrx in A_d.
      rewrite assoc.get_union_sing_neq; last first.
        move=> ?; subst x.
        apply assoc.get_Some_in_dom in Hrx.
        by rewrite Hrx in y_d.
      rewrite assoc.get_union_sing_neq //.
        move=> ?; subst x.
        apply assoc.get_Some_in_dom in Hrx.
        by rewrite Hrx in z_d.
    suff <- : heap_mint rx st h = heap_mint rx st' h'.
      apply (proj2 s_st_h x y) => //.
      by assoc_get_Some.
    apply (heap_mint_state_invariant (heap_mint mA st h \U
      heap_mint my st h \U heap_mint mz st h) x s) => //.
    - move=> x0 Hx0.
      apply H1 with rx => //.
      by apply assoc.get_Some_in_cdom with x.
    - by apply (proj1 s_st_h).
    - apply heap.disjhU.
      + apply heap.disjhU.
        * apply (proj2 s_st_h x A) => //.
          - move=> ?; subst x.
            apply assoc.get_Some_in_dom in Hrx.
            by rewrite Hrx in A_d.
          - by assoc_get_Some.
        * apply (proj2 s_st_h x y) => //.
          by assoc_get_Some.
      + apply (proj2 s_st_h x z) => //.
        * move=> ?; subst x.
          apply assoc.get_Some_in_dom in Hrx.
          by rewrite Hrx in z_d.
        * by assoc_get_Some.
case/assoc.get_union_Some_inv : Hry0 => Hry0.
  case/assoc.get_sing_inv : Hry0 => ? ?; subst y0 ry0.
    rewrite heap.disjE dom_rz -heap.disjE.
    have Htmp : assoc.get x (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) = Some rx.
      rewrite assoc.get_union_sing_neq; last first.
        move=> ?; subst x.
        apply assoc.get_Some_in_dom in Hrx.
        by rewrite Hrx in A_d.
      rewrite assoc.get_union_sing_neq; last first.
        move=> ?; subst x.
        apply assoc.get_Some_in_dom in Hrx.
        by rewrite Hrx in y_d.
      by rewrite assoc.get_union_sing_neq.
    suff <- : heap_mint rx st h = heap_mint rx st' h'.
      apply (proj2 s_st_h x z) => //.
      by assoc_get_Some.
    apply (heap_mint_state_invariant (heap_mint mA st h \U
      heap_mint my st h \U heap_mint mz st h) x s) => //.
    - move=> x0 Hx0.
      apply H1 with rx => //.
      by apply assoc.get_Some_in_cdom with x.
    - by apply (proj1 s_st_h).
    - apply heap.disjhU.
      + apply heap.disjhU.
        * apply (proj2 s_st_h x A) => //.
          move=> ?; subst x.
          apply assoc.get_Some_in_dom in Hrx.
          by rewrite Hrx in A_d.
          by assoc_get_Some.
        * apply (proj2 s_st_h x y) => //.
          move=> ?; subst x.
          apply assoc.get_Some_in_dom in Hrx.
          by rewrite Hrx in y_d.
          by assoc_get_Some.
      + apply (proj2 s_st_h x z) => //.
        by assoc_get_Some.
have Htmp : assoc.get x (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) = Some rx.
  rewrite assoc.get_union_sing_neq; last first.
    move=> ?; subst x.
    apply assoc.get_Some_in_dom in Hrx.
    by rewrite Hrx in A_d.
  rewrite assoc.get_union_sing_neq; last first.
    move=> ?; subst x.
    apply assoc.get_Some_in_dom in Hrx.
    by rewrite Hrx in y_d.
  rewrite assoc.get_union_sing_neq //.
    move=> ?; subst x.
    apply assoc.get_Some_in_dom in Hrx.
    by rewrite Hrx in z_d.
have <- : heap_mint rx st h = heap_mint rx st' h'.
  apply (heap_mint_state_invariant (heap_mint mA st h \U
        heap_mint my st h \U heap_mint mz st h) x s) => //.
  - move=> x0 Hx0.
    apply H1 with rx => //.
    by apply assoc.get_Some_in_cdom with x.
  - by apply (proj1 s_st_h x).
  - apply heap.disjhU.
    + apply heap.disjhU.
      * apply (proj2 s_st_h x A) => //.
        move=> ?;subst x.
        apply assoc.get_Some_in_dom in Hrx.
        by rewrite Hrx in A_d.
        by assoc_get_Some.
      * apply (proj2 s_st_h x y) => //.
        move=> ?; subst x.
        apply assoc.get_Some_in_dom in Hrx.
        by rewrite Hrx in y_d.
        by assoc_get_Some.
    + apply (proj2 s_st_h x z) => //.
      move=> ?; subst x.
      apply assoc.get_Some_in_dom in Hrx.
      by rewrite Hrx in z_d.
      by assoc_get_Some.
have Htmp2 : assoc.get y0 (A |=> mA \U+ (y |=> my \U+ (z |=> mz \U+ d))) = Some ry0.
  rewrite assoc.get_union_sing_neq; last first.
    move=> ?; subst y0.
    apply assoc.get_Some_in_dom in Hry0.
    by rewrite Hry0 in A_d.
  rewrite assoc.get_union_sing_neq; last first.
    move=> ?; subst y0.
    apply assoc.get_Some_in_dom in Hry0.
    by rewrite Hry0 in y_d.
  rewrite assoc.get_union_sing_neq //.
  move=> ?; subst y0.
  apply assoc.get_Some_in_dom in Hry0.
  by rewrite Hry0 in z_d.
suff <- : heap_mint ry0 st h = heap_mint ry0 st' h'.
  by apply (proj2 s_st_h x y0).
apply (heap_mint_state_invariant (heap_mint mA st h \U
      heap_mint my st h \U heap_mint mz st h) y0 s) => //.
  move=> x0 Hx0.
  apply H1 with ry0 => //.
  by apply assoc.get_Some_in_cdom with y0.
  exact: (proj1 s_st_h).
  apply heap.disjhU.
  - apply heap.disjhU.
    + apply (proj2 s_st_h y0 A) => //.
      move=> ?; subst y0.
      apply assoc.get_Some_in_dom in Hry0.
      by rewrite Hry0 in A_d.
      by assoc_get_Some.
    + apply (proj2 s_st_h y0 y) => //.
      move=> ?; subst y0.
      apply assoc.get_Some_in_dom in Hry0.
      by rewrite Hry0 in y_d.
      by assoc_get_Some.
    + apply (proj2 s_st_h y0 z) => //.
      move=> ?; subst y0.
      apply assoc.get_Some_in_dom in Hry0.
      by rewrite Hry0 in z_d.
      by assoc_get_Some.
Qed.

(*Definition sim d := fwd_sim (state_mint d).
Definition psim d := pfwd_sim (state_mint d).
Definition sim_b b pre post d := b <=b( state_mint d ) pre ; post.*)

Local Close Scope heap_scope.

Local Notation "k '#' m" := (syntax_m.seplog_m.assert_m.expr_m.store.store.disj k m).
Local Notation "k '\U' m" := (syntax_m.seplog_m.assert_m.expr_m.store.store.union k m).
Local Notation "k '\D\' m" := (syntax_m.seplog_m.assert_m.expr_m.store.store.difs k m).
Local Notation "k '\d\' m" := (syntax_m.seplog_m.assert_m.expr_m.store.store.dif k m).
Local Notation "k '|P|' m" := (syntax_m.seplog_m.assert_m.expr_m.store.store.proj k m).

Lemma state_mint_inj d s st h s' :
  inc (assoc.dom d) (syntax_m.seplog_m.assert_m.expr_m.store.store.dom s) ->
  inc (assoc.dom d) (syntax_m.seplog_m.assert_m.expr_m.store.store.dom s') ->
  state_mint d s st h -> state_mint d s' st h ->
  s |P| (assoc.dom d) = s' |P| (assoc.dom d).
Proof.
rewrite /state_mint => ds ds'.
move=> [s_st_h1 s_st_h2] [s'_st_h1 s'_st_h2].
apply syntax_m.seplog_m.assert_m.expr_m.store.extensionality => //.
move => x xd.
have [X|[rx X]] : assoc.get x d = None \/ exists rx, assoc.get x d = Some rx.
  case: (assoc.get x d); [move=> rx_; right; by exists rx_ | by auto].
- (*rewrite !syntax_m.seplog_m.assert_m.expr_m.store.get_proj' //.
  by apply assoc.get_None_notin.
  by apply assoc.get_None_notin.*)
  move/assoc.in_dom_get_Some in xd.
  case: xd => x0.
  by rewrite X.
- move: (s_st_h1 _ _ X) => x_s_rx.
  move: (s'_st_h1 _ _ X) => x_s'_rx.
  destruct rx as [rk rx|rx].
  - case : (x_s_rx) => x_s_over rx_mem rx_fit.
    case : (x_s'_rx) => _(*same as rx_fit*) x_s'_over rx'_mem.
    have Htmp : ([ x ]_ s = [ x ]_ s')%pseudo_expr.
      have Htmp : Z2ints 32 (Z.abs_nat (u2Z ([rk ]_ st)%asm_expr)) ([ x ]_ s)%pseudo_expr =
        Z2ints 32 (Z.abs_nat (u2Z ([rk ]_ st)%asm_expr)) ([ x ]_ s')%pseudo_expr.
      eapply assert_m.mapstos_inj.
      by rewrite size_Z2ints.
      by rewrite size_Z2ints.
      by apply x_s_rx.
      exact rx'_mem.
      by apply Z2ints_inj in Htmp.
    by [].
(*    rewrite !syntax_m.seplog_m.assert_m.expr_m.store.get_proj //.
    by eapply assoc.get_Some_in_dom; eauto.
    by eapply assoc.get_Some_in_dom; eauto.*)
  - case : (x_s_rx) => slen ptr A rx_2_fit encodingA ptr_fit mem.
    case : (x_s'_rx) => slen' ptr' A' _ (*same as rx_2_fit*) encodingA' ptr'_fit mem'.
(*    rewrite !syntax_m.seplog_m.assert_m.expr_m.store.get_proj //; last 2 first.
      by eapply assoc.get_Some_in_dom; eauto.
      by eapply assoc.get_Some_in_dom; eauto.*)
    have : slen = slen'.
      move/con_heap_mint_signed_con_TT : mem.
      rewrite assert_m.conAE; move/assert_m.mapsto_con_get => mem.
      move/con_heap_mint_signed_con_TT : mem'.
      rewrite assert_m.conAE; move/assert_m.mapsto_con_get => mem'.
      rewrite mem in mem'; by case: mem'.
    move=> ?; subst slen'.
    have : ptr = ptr'.
      rewrite assert_m.conAE assert_m.conCE 2!assert_m.conAE in mem.
      move/con_heap_mint_signed_con_TT : mem.
      move/assert_m.mapsto_con_get => mem.
      rewrite assert_m.conAE assert_m.conCE 2!assert_m.conAE in mem'.
      move/con_heap_mint_signed_con_TT : mem'.
      move/assert_m.mapsto_con_get => mem'.
      rewrite mem /= in mem'; by case: mem'.
    move=> ?; subst ptr'.
    case: (Z_zerop (s2Z slen)) => slen_neq0.
      case: encodingA => ? ? ? ->.
      case: encodingA' => ? ? ? ->.
      by rewrite slen_neq0.
    move: mem; rewrite assert_m.conCE; move/con_heap_mint_signed_con_TT => mem.
    move: mem'; rewrite assert_m.conCE; move/con_heap_mint_signed_con_TT => mem'.
    rewrite -/([ int_e ptr ]e_st)%asm_expr in ptr_fit.
    case: encodingA => A_nk ? ? ?.
    case: encodingA' => A'_nk ? ? ?.
    move: (assert_m.mapstos_con_inj _ _ _ _ _ _ _ _ ptr_fit A_nk A'_nk mem mem') => H.
    subst A'.
    congruence.
Qed.

Local Notation "'dom' k" := (syntax_m.seplog_m.assert_m.expr_m.store.store.dom k) (at level 4).

Lemma transport d p c I0 : safe_termination (state_mint d) c ->
  terminating p ->
  List.incl (syntax_m.cmd_vars p) (assoc.dom d)  ->
    forall encode decode,
      (forall s, state_mint d s (fst (encode d s)) (snd (encode d s))) ->
      (forall st he, state_mint d (decode d (st, he)) st he /\
        dom (decode d (st, he)) = assoc.dom d) ->
  p <=p(state_mint d, I0) c ->
  forall (P0 Pf : syntax_m.seplog_m.assert_m.assert),
    syntax_m.seplog_m.hoare_m.hoare P0 p Pf ->
    forall s,
        ({{ fun st h => encode d s = (st, h) /\ P0 s syntax_m.seplog_m.assert_m.heap.emp /\ I0 s st h }} c
         {{ fun st' h' => Pf
           (decode d (st', h') \U (s \D\ assoc.dom d))
           syntax_m.seplog_m.assert_m.heap.emp }})%asm_hoare.
Proof.
move=> Hsafe_term Hterm Hincl enc dec Henc Hdec Hsim_c_c P0 Pf Hhoare_c s.
apply mips_seplog.hoare_prop_m.hoare_complete => /= st h [H_s_st_h [HP0 HI0]]; split.
- move=> Habsurd.
  rewrite /safe_termination in Hsafe_term.
  lapply (Hsafe_term s st h); last first.
    rewrite -/(fst (st, h)) -{2}/(snd (st, h)) -H_s_st_h.
    by apply Henc.
  case=> s' Hs'.
  by move: (mips_syntax.semop_deter_prop_m.exec_deter _ _ _ Hs' _ Habsurd).
- move=> st' h' Hexec_asm.
  move/syntax_m.seplog_m.soundness : Hhoare_c.
  case/(_ _ _ HP0) => _ Hhoare_c.
  apply Hhoare_c.
  move=> {Hhoare_c HP0}.
  apply pfwd_sim_fwd_sim_spec in Hsim_c_c => //.
  apply fwd_sim_bck_sim in Hsim_c_c => //.
  move=> {Hsafe_term}.
  rewrite /bck_sim in Hsim_c_c.
  have Hs_encode_s : state_mint d s (fst (enc d s)) (snd (enc d s)).
    move: (Henc s).
    by destruct (enc d s).
  move=> {Henc}.
  destruct (enc d s) as [s1 s2].
  case: H_s_st_h => Hs1 Hs2; subst s1 s2.
  case: {Hsim_c_c Hexec_asm}(Hsim_c_c _ _ _ Hs_encode_s HI0 _ _ Hexec_asm) => s' [] Hs' H.
  move: {Hdec}(Hdec st' h') => [Hdec Hdec2].
  have ds' :  inc (assoc.dom d) (dom s').
    admit.
  have ddec : inc (assoc.dom d) (dom (dec d (st', h'))).
    by rewrite Hdec2 inc_refl.
  move: {Hdec}(state_mint_inj _ _ _ _ _ ds' ddec H Hdec) => Hinj.
  have -> : dec d (st', h') = (dec d (st', h')) |P| (assoc.dom d).
    rewrite -Hdec2.
    by rewrite syntax_m.seplog_m.assert_m.expr_m.store.store.proj_itself.
  have -> : s \D\ (assoc.dom d) = s' \D\ (assoc.dom d).
    simpl in Hs_encode_s.
Abort. (* TODO: FIXME *)
(*    apply syntax_m.seplog_m.assert_m.expr_m.store.extensionality => v.
    case/orP : (orbN (v \in assoc.dom d)) => X.
    + rewrite syntax_m.seplog_m.assert_m.expr_m.store.get_difs' //.
      by rewrite syntax_m.seplog_m.assert_m.expr_m.store.get_difs'.
    + rewrite syntax_m.seplog_m.assert_m.expr_m.store.get_difs //.
      rewrite syntax_m.seplog_m.assert_m.expr_m.store.get_difs //.
      Var_unchanged.
      move/syntax_m.In_cmd_vars/inP/Hincl/inP; exact/negP.
  by rewrite -Hinj -syntax_m.seplog_m.assert_m.expr_m.store.store.proj_difs.
Qed.*)

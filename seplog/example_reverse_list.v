(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext uniq_tac.
Require Import bipl seplog.

Require Import integral_type.
Module Import seplog_Z_m := Seplog ZIT.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.

Local Open Scope Z_scope.
Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.

(** the mandatory reverse list program *)

(** the fields of the cell structure *)
Definition data := 0.
Definition next := 1.

(** i points to the input list
    rem points to the remainder of the input list (what's left to be processed)
    ret points to the output list (the reversed "head") *)
Definition reverse_list (i ret rem : var.v) :=
  ret <- nat_e 0 ;
  while.while ( var_e i \!= nat_e 0 ) (
       rem <-* (i -.> next) ;
       (i -.> next) *<- var_e ret ;
       ret <- var_e i ;
       i <- var_e rem
  ).

(** this assertion represents the fact that a list begin at some address i and
    ends pointing to some address j *)
Inductive list_seplog : seq Z -> nat -> nat -> assert :=
| list_end : forall l i j s h,
  assert_m.emp s h ->
  i = j ->
  l = nil ->
  list_seplog l i j s h
| list_next : forall l i k s h hd tl j h1 h2,
  h1 # h2 ->
  h = h1 \U h2 ->
  i <> k ->
  i <> j ->
  l = hd :: tl ->
  (nat_e i |--> cst_e hd :: nat_e j :: nil) s h1 ->
  list_seplog tl j k s h2 ->
  list_seplog l i k s h.

Lemma list_seplog_ext l i j s1 s2 h : list_seplog l i j s1 h -> list_seplog l i j s2 h.
Proof. elim; clear l i j s1 h; move=> *; by [constructor | econstructor 2; eauto]. Qed.

Lemma list_seplog_hd_neq l1 l2 hd1 hd2 s h :
  (list_seplog l1 hd1 0 ** list_seplog l2 hd2 0) s h -> hd1 <> O -> hd1 <> hd2.
Proof.
move=> H H0.
case_sepcon H.
inversion_clear H_h1 as [| l l' d i j k s0 h0 h1_ h2_ H H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11]; subst => //.
inversion H_h2; subst => //.
rewrite /= in H5; case_sepcon H5.
rewrite /= in H10; case_sepcon H10.
case : H5_h1_1 => [x1 [/= Hx1 H20]].
case : H10_h11 => [x2 [/= Hx2 H18]].
subst x1 x2.
have : h11 # h1_1 by map_tac_m.Disj.
rewrite H18 H20; move/heap.disj_sing' => X.
by apply/eqP; apply: contra X => /eqP ->.
Qed.

(** we consider well-formed lists to be terminated by the NULL pointer *)
Definition reverse_condition l hd : assert := fun s h =>
  exists v, [ var_e hd ]e_ s = Z_of_nat v /\ list_seplog l v 0 s h.

Local Open Scope uniq_scope.

Definition reverse_list_specif : Prop := forall l (i j k : nat), uniq(i, j, k) ->
    {{ reverse_condition l i }} reverse_list i j k {{ reverse_condition (rev l) j }}.

(** reverse_list verification *)

Lemma reverse_list_verif : reverse_list_specif.
Proof.
rewrite /reverse_list_specif /reverse_list /reverse_condition => l i ret rem H.
(** ret <- nat_e 0; *)
apply hoare_assign with (fun s h => exists v,
  [ i ]_ s = Z_of_nat v /\ list_seplog l v 0 s h /\ [ ret ]_ s = Z_of_nat 0).
move=> s h [x [/= Hi Hl]]; rewrite /wp_assign; exists x => /=.
repeat Store_upd.
repeat (split => //).
by move: Hl; apply list_seplog_ext.
(** while (var_e i <>e nat_e 0) *)
apply hoare_prop_m.hoare_while_invariant with (fun s h => exists l1 l2,
  l = l1 ++ l2 /\ exists v_i v_ret,
    [ var_e i ]e_ s = Z_of_nat v_i /\  [ ret ]_ s = Z_of_nat v_ret /\
    (list_seplog l2 v_i 0 ** list_seplog (rev l1) v_ret 0) s h).
- move=> s h [x [Hi [Hl Hj]]].
  exists nil, l; split; first by [].
  exists x, O; repeat (split => //).
  Compose_sepcon h heap.emp => //.
  by constructor.
- move=> s h /= [[l1 [l2 [Hl [vi [vj [H2 [H3 [h1 [h2 [Hdisj [Hunion [Hlist_h1 Hlist_h2]]]]]]]]]]]] Hi_0].
  move/negPn/eqP in Hi_0; rewrite /= in Hi_0.
  have : vi = O by rewrite Hi_0 in H2 ; destruct vi.
  move=> ?; subst vi.
  inversion_clear Hlist_h1 => //; subst l2.
  rewrite cats0 in Hl; subst l1.
  exists vj; split; first by [].
  by rewrite Hunion H0 heap.unioneh.
(** rem <-* i -.> next; *)
apply hoare_prop_m.hoare_stren with (fun s h => exists l1 l2,
  exists elt, l = l1 ++ elt :: l2 /\ exists v_i v_ret, [ i ]_ s = Z_of_nat v_i /\
    [ ret ]_ s = Z_of_nat v_ret /\ v_i <> O /\ v_i <> v_ret /\
    (list_seplog (elt :: l2) v_i 0 ** list_seplog (rev l1) v_ret 0) s h).
move=> s h /= [[l1 [l2 [Hl [x1 [x2 [Hi [Hj Hmem]]]]]]] /negbTE/eqP Hi'].
rewrite /= in Hi'.
case_sepcon Hmem.
inversion_clear Hmem_h1.
- have [//] : x1 <> O by move=> X; subst; rewrite Hi in Hi'.
- subst l2.
  exists l1, tl, hd; split; first by [].
  exists x1, x2; repeat (split => //).
  + apply (list_seplog_hd_neq (hd :: tl) (rev l1) _ _ s h); last by lia.
    Compose_sepcon h1 h2 => //.
    by eapply list_next; eauto.
  + Compose_sepcon h1 h2 => //.
    by eapply list_next; eauto.
apply hoare_lookup_back'' with (fun s h => exists l1 l2,
  exists elt, l = l1 ++ elt :: l2 /\ exists v_i v_ret v_rem,
    [ i ]_ s = Z_of_nat v_i /\ [ ret ]_ s = Z_of_nat v_ret /\ [ rem ]_ s = Z_of_nat v_rem /\
    v_i <> O /\  v_i <> v_ret /\
    (list_seplog (elt :: nil) v_i v_rem ** list_seplog l2 v_rem 0 ** list_seplog (rev l1) v_ret 0) s h).
move=> s h /= [l1 [l2 [elt [Hl [vi [vj [Hi [Hj [Hvi_not_0 [Hvi_not_vj Hmem]]]]]]]]]].
case_sepcon Hmem.
inversion_clear Hmem_h1 => //.
case: H4 => X Y; subst hd tl.
rewrite /= in H5; case_sepcon H5.
move/assert_m.con_emp : H5_h32 => H5_h32.
exists (nat_e j).
Compose_sepcon h32 (h31 \U h4 \U h2).
  rewrite /next; by Mapsto.
apply mapsto_strictly_exact' with h32; last 2 first.
  by map_tac_m.Disj.
  rewrite /next; by Mapsto.
rewrite /wp_assign.
exists l1, l2, elt; split; first by [].
repeat Store_upd.
exists vi, vj, j; repeat (split => //).
Compose_sepcon (h31 \U h32) (h4 \U h2).
-  apply list_seplog_ext with s.
   apply (list_next _ _ _ _ _ elt nil j (h31 \U h32) heap.emp) => //.
   by map_tac_m.Disj.
   by map_tac_m.Equal.
   Compose_sepcon h31 h32.
   by Mapsto.
   rewrite /=; apply assert_m.con_emp'; by Mapsto.
   by apply list_end.
- Compose_sepcon h4 h2.
  + move: H6; by apply list_seplog_ext.
  + move: Hmem_h2; by apply list_seplog_ext.
(** i -.> next *<- var_e ret ; *)
apply hoare_mutation_backwards'' with (fun s h => exists l1 l2,
  exists elt, l = l1 ++ (elt :: l2) /\ exists v_i v_rem, [ i ]_ s = Z_of_nat v_i /\
    [ rem ]_ s = Z_of_nat v_rem /\ v_i <> O /\
      (list_seplog (rev (l1 ++ elt :: nil)) v_i 0 ** list_seplog l2 v_rem 0) s h).

move=> s h /= [l1 [l2 [elt [Hl [vi [vj [vk [Hvi [Hvj [Hvk [Hvi_not_0 [Hvi_not_vj Hmem]]]]]]]]]]]].
case_sepcon Hmem.
case_sepcon Hmem_h2.
inversion_clear Hmem_h1 => //.
case: H4 => ? ?; subst hd tl.
inversion_clear H6 => //; subst j; clear H8.
rewrite /= in H5; case_sepcon H5.
move/assert_m.con_emp : H5_h32 => H5_h32.
exists (nat_e vk).
Compose_sepcon h32 (h21 \U h31 \U h22).
  rewrite /next; by Mapsto.
rewrite /imp => h32' [X1 X2] h' Hh'.
exists l1, l2, elt; split; first by [].
exists vi, vk; repeat (split=> //).
Compose_sepcon (h22 \U h31 \U h32') h21 => //.
rewrite rev_cat /=.
apply (list_next _ _ _ _ _ elt (rev l1) vj (h31 \U h32') h22) => //.
- by map_tac_m.Disj.
- by map_tac_m.Equal.
- Compose_sepcon h31 h32'.
  by Mapsto.
  rewrite /=; apply assert_m.con_emp'; rewrite /next in X2; by Mapsto.
(** ret <- var_e i; *)
apply hoare_assign with (fun s h => exists l1 l2 elt,
  l = l1 ++ elt :: l2 /\ exists v_j v_rem,
    [ ret ]_ s = Z_of_nat v_j /\ [ rem ]_ s = Z_of_nat v_rem /\
      (list_seplog (rev (l1 ++ elt :: nil)) v_j 0 ** list_seplog l2 v_rem 0) s h).
move=> s h /= [l1 [l2 [elt [H0 [vi [vj [H1 [H4 [H3 [h1 [h2 [Hdisj [Hunion [H5 H6]]]]]]]]]]]]]].
rewrite /wp_assign /=.
exists l1, l2, elt; split; first by [].
exists vi, vj; repeat Store_upd => //; repeat (split => //).
by Compose_sepcon h1 h2; eapply list_seplog_ext; eauto.
(** i <- var_e rem *)
apply hoare_assign'.
move=> s h /= [l1 [l2 [elt [H0 [vj [vk [H1 [H4 [h1 [h2 [Hdisj [Hunion [ H5 H6]]]]]]]]]]]]].
rewrite /wp_assign /=; exists (l1 ++ elt :: nil), l2; split => //.
by rewrite -catA.
exists vk, vj; repeat Store_upd; repeat (split => //).
by Compose_sepcon h2 h1; eapply list_seplog_ext; eauto.
Qed.

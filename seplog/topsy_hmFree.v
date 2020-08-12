(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext ZArith Lia.
Require Import bipl seplog integral_type.
Require Import topsy_hm topsy_hmFree_prg.

Require Import expr_b_dp.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.

Local Close Scope Z_scope.
Local Close Scope positive_scope.
Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_hoare_scope.

Definition hmFree_specif := forall p x sizex y sizey statusy, p > 0 ->
  {{ fun s h => exists l, (Heap_List l p ** Array (x + 2) sizex) s h /\
     In_hl l (x, sizex, alloc) p /\ In_hl l (y, sizey, statusy) p /\
     x <> y /\ [ var_e hmStart \= nat_e p ]b_s }}
  hmFree (x + 2) entry cptr nptr result
  {{ fun s h => exists l, Heap_List l p s h /\
     In_hl l (x, sizex, topsy_hm.free) p /\ In_hl l (y, sizey, statusy) p /\
     [ var_e result \= HM_FREEOK ]b_s }}.

Lemma hmFree_verif : hmFree_specif.
Proof.
rewrite /hmFree_specif /hmFree => p x sizex y sizey statusy H.

Step (fun s h => exists l, (Heap_List l p ** Array (x + 2) sizex) s h /\
  In_hl l (x, sizex, alloc) p /\  In_hl l (y, sizey, statusy) p /\
  x <> y /\ [ var_e hmStart \= nat_e p ]b_s /\ [ var_e entry \= nat_e p ]b_s).

rewrite /wp_assign.
case: H0 => x0 [H1 [H2 [H3 [H4 H5]]]].
exists x0; split.
case_sepcon H1.
Compose_sepcon h1 h2.
by Heap_List_equiv.
by Array_equiv.
by Resolve_topsy.

Step (fun s h => exists l, (Heap_List l p ** Array (x + 2) sizex) s h /\
  In_hl l (x, sizex, alloc) p /\ In_hl l (y, sizey, statusy) p /\
  x <> y /\
  [ var_e hmStart \= nat_e p ]b_s /\ [ var_e entry \= nat_e p ]b_s /\
  [ var_e cptr \= nat_e x ]b_s).

rewrite /wp_assign.
case: H0 => x0 [H1 [H2 [H3 [H4 [H5 H6]]]]].
exists x0.
split.
case_sepcon H1.
Compose_sepcon h1 h2.
by Heap_List_equiv.
by Array_equiv.
by Resolve_topsy.

Step (fun s h => exists l,
  (Heap_List l p ** Array (x + 2) sizex) s h /\
  In_hl l (x, sizex, alloc) p /\ In_hl l (y, sizey, statusy) p /\
  x <> y /\
  [ var_e hmStart \= nat_e p ]b_s /\ [ var_e cptr \= nat_e x ]b_s /\
  exists l1 size stat l2,
    l = l1 ++ (size, stat) :: l2 /\
    [ var_e entry \= nat_e (get_endl l1 p) ]b_s /\
    ~ In_hl l1 (x, sizex, alloc) p).

case: H0 => x0 [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
exists x0.
split.
exact H1.
Resolve_topsy.
destruct x0.
by rewrite /= in H3.
destruct p0 as [n b].
exists nil, n, b, x0.
by Resolve_topsy.

Step (fun s h => exists l,
  (Heap_List l p ** Array (x + 2) sizex) s h /\
  In_hl l (x, sizex, alloc) p /\ In_hl l (y, sizey, statusy) p /\
  x <> y /\
  [ var_e hmStart \= nat_e p ]b_s /\
  [ var_e cptr \= nat_e x ]b_s /\
  exists l1 size stat l2,
    l = l1 ++ (size,stat) :: l2 /\
    [ var_e entry \= nat_e (get_endl l1 p) ]b_s /\
    [ var_e nptr \= nat_e (get_endl l1 p + size + 2) ]b_s /\
    [ var_e entry \!= null \&& var_e entry \!= var_e cptr ]b_s /\
    ~ In_hl l1 (x, sizex, alloc) p).

case: H0 => [[x0 [H0 [H2 [H3 [H4 [H5 [H6 [x1 [x2 [x3 [x4 [H7 [H8 H9]]]]]]]]]]]]] H1].
exists (nat_e (get_endl x1 p + x2 + 2)).
case_sepcon H0.
apply mapsto_strictly_exact; split.
rewrite H7 in H0_h1; move/hl_getnext : H0_h1 => H15.
case_sepcon H15.
Compose_sepcon h11 (h12 \U h2); last by done.
rewrite /next; by Mapsto.
rewrite /wp_assign.
exists x0; split.
Compose_sepcon h1 h2.
by Heap_List_equiv.
by Array_equiv.
Resolve_topsy.
exists x1, x2, x3, x4; by Resolve_topsy.

(* xxx *)

Step TT.
move=> s h [l [H1 [H2 [H3 [H4 [H5 [H6 [l1 [size [stat [l2 [H7 [H8 [H9 [H10 H11]]]]]]]]]]]]]]].
rewrite /wp_assign.
exists l; split.
case_sepcon H1.
Compose_sepcon h1 h2.
by eapply Heap_List_inde_store; apply H1_h1.
by Array_equiv.
Resolve_topsy.
destruct l2.
- rewrite H7 in H2; case/In_hl_app_or : H2 => // /=.
  case: ifP => //.
  case/andP => /andP [] /eqP ? _ _.
  exfalso; by omegab.
- destruct p0.
  exists (l1 ++ (size, stat) :: nil), n, b, l2; split.
  by rewrite -catA.
  split.
  rewrite get_endl_app [get_endl _ _]/= eval_b_upd_subst; omegab.
  case/In_hl_app_or => H12.
  + tauto.
  + rewrite /= in H12.
    case: ifP H12 => //.
    case/andP => /andP [] /eqP ? _ _.
    exfalso; by omegab.

Step TT.

Step (fun s h => exists l, (Heap_List l p ** Array (x + 2) sizex) s h /\
  In_hl l (x, sizex, alloc) p /\
  In_hl l (y, sizey, statusy) p /\
  x <> y /\
  [ var_e hmStart \= nat_e p ]b_s /\
  [ var_e cptr \= nat_e x ]b_s /\
  (exists l1 size stat, (exists l2,
    l = l1 ++ (size, stat) :: l2 /\
    [ var_e entry \= nat_e (get_endl l1 p) ]b_s /\
    ~ In_hl l1 (x, sizex, alloc) p) /\
  [ var_e entry \!= null ]b_s /\
  (~~ [var_e entry \!= var_e cptr]b_s) /\
  [ var_e nptr \= nat_e (get_endl (l1 ++ (size, stat) :: nil) p) ]b_s)).

case: H0 => [[[l [H2 [H3 [H4 [H5 [H6 [H7 [l1 [size [stat [l2 [H9 [H10 H11]]]]]]]]]]]]] H1] H0].
exists (nat_e (get_endl (l1 ++ (size, stat) :: nil) p)).
case_sepcon H2.
apply mapsto_strictly_exact; split.
rewrite H9 in H2_h1; move/hl_getnext : H2_h1 => H15.
case_sepcon H15.
Compose_sepcon h11 (h12 \U h2); last by done.
rewrite /next get_endl_app; by Mapsto.
rewrite /wp_assign.
exists l; split.
Compose_sepcon h1 h2.
by Heap_List_equiv.
by Array_equiv.
Resolve_topsy.
exists l1, size, stat; split.
exists l2; split; first by done.
split.
rewrite eval_b_upd_subst; omegab.
assumption.
split.
rewrite eval_b_upd_subst; omegab.
split; rewrite eval_b_upd_subst; omegab.

Step TT.

Step (fun s h => exists l, Heap_List l p s h /\
  In_hl l (x, sizex, topsy_hm.free) p /\
  In_hl l (y, sizey, statusy) p /\
  x <> y /\
  [ var_e hmStart \= nat_e p ]b_s /\
  [ var_e cptr \= nat_e x ]b_s /\
  exists l1 size stat, (exists l2,
    l = l1 ++ (size, stat) :: l2 /\
    [ var_e entry \= nat_e (get_endl l1 p) ]b_s /\
    ~ In_hl l1 (x, sizex, alloc) p) /\
  [ var_e entry \!= null ]b_s /\
  (~~[var_e entry \!= var_e cptr]b_s) /\
  [ var_e nptr \= nat_e (get_endl (l1 ++ (size, stat) :: nil) p) ]b_s).

case : H0 => [[l [H1 [H2 [H3 [H4 [H5 [H6 [l1 [size [stat [[l2 [H8 [H9 H10]]] [H11 [H12 H13]]]]]]]]]]]]] H0].

have [H15 H16] : sizex = size /\ alloc = stat.
  rewrite H8 (_ : x = get_endl l1 p) in H2; last by omegab.
  by apply In_hl_match in H2.
subst size stat.

rewrite /status.
rewrite H8 /alloc in H1.
have H11' : get_endl l1 p = x by omegab.
rewrite -H11' in H1.
case: (hl_alloc2free _ _ _ _ _ _ H1) => x2 H16.
exists x2.
case_sepcon H16.
Compose_sepcon h1 h2.
by Mapsto.
move=> h1' [X1 X2] h' Hh'.
exists (l1 ++ (sizex, true) :: l2).
split.
  eapply H16_h2.
  split; [by apply X1 | by Mapsto].
  assumption.
split.
  apply In_hl_or_app.
  right.
  by rewrite /= H11' !eqxx.
split.
  rewrite H8 in H3.
  case/In_hl_app_or : H3 => H3.
  - apply In_hl_or_app; by left.
  - rewrite /= in H3.
    case: ifP H3 => //.
      case/andP => /andP [/eqP ?] _ _; exfalso; lia. 
    move=> ? ?.
    apply In_hl_or_app; right => /=.
    by case: ifP.
split; first by done.
split; first by omegab.
split; first by omegab.
exists l1, sizex, true; split.
exists l2; split; first by done.
split; first by omegab.
done.
split; first by omegab.
split; first by omegab.
rewrite 2!get_endl_app in H13 *; by omegab.

Step TT.

move=> s h [l [H0 [H1 [H2 [H3 [H4 [H5 [l1 [size [stat [H6 [H7 [H8 H9]]]]]]]]]]]]].
rewrite /wp_assign.
exists l; split.
by eapply Heap_List_inde_store; apply H0.
split; first by done.
split; first by done.
by rewrite eval_b_upd_subst; omegab.

Step TT.
move=> s h [[l [H1 [H2 [H3 [H4 [H5 [H6 [l1 [size [stat [[l2 [H7 [H8 H9]]] [H10 [H11 H12]]]]]]]]]]]]] H0].
rewrite get_endl_app [get_endl _]/= in H12.
exfalso. omegab.

Step TT.
rewrite /wp_assign; move=> s h [[[l [H3 [H4 [H5 [H6 [H7 [H8 [l1 [size [stat [l2 [H9 [H10 H11]]]]]]]]]]]]] H1] H2].
destruct l1.
- exfalso. omegab.
- destruct p0.
  rewrite [get_endl _ _]/= in H10.
  move: (get_endl_gt l1 (p + 2 + n)) => H15.
  exfalso. omegab.
Qed.

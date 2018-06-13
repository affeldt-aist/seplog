(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ZArith_ext ssrnat_ext.
Require Import bipl seplog.
Require Import topsy_hm topsy_hmAlloc_prg topsy_hmAlloc.

Require Import integral_type.

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

Definition hmAlloc_example (result entry cptr fnd stts nptr sz : var.v) (v : Z) :=
  hmAlloc result 1 entry cptr fnd stts nptr sz;
  If (var_e result \!= nat_e 0) Then (
    (var_e result *<- cst_e v)
  ) Else ( skip  ).

Definition hmAlloc_example_specif := forall v x e p, p > 0 ->
{{ (nat_e x |~> cst_e e) **
   (fun s h => exists l, [ var_e hmStart \= nat_e p ]b_s /\ Heap_List l p s h /\ In_hl l (x, 1, alloc) p) }}
hmAlloc_example result entry cptr fnd stts nptr sz v
{{ fun s h => [ var_e result \!= nat_e 0 ]b_s ->
   ((nat_e x |~> cst_e e) **
    (fun s h => exists l, Heap_List l p s h /\ In_hl l (x, 1, alloc) p) **
    (var_e result |~> cst_e v) ** TT) s h}}.

Lemma hmAlloc_example_verif : hmAlloc_example_specif.
Proof.
rewrite /hmAlloc_example_specif => v x e p H.
rewrite /hmAlloc_example.

Step ((fun s h => (exists l y, y > 0 /\ [ var_e result \= nat_e (y + 2) ]b_s /\
  (exists size'', size'' >= 1 /\
    (Heap_List l p ** Array (y + 2) size'') s h /\
    In_hl l (x, 1, alloc) p /\
    In_hl l (y, size'', alloc) p /\
    x <> y)) \/
  exists l, [ var_e result \= nat_e 0 ]b_s /\ Heap_List l p s h /\ In_hl l (x, 1, alloc) p) **
(nat_e x |~> cst_e e)).

Frame_rule (nat_e x |~> cst_e e).

have H0 : 1 > 0. ssromega.
move: (hmAlloc_verif p x 1 1 H H0) => {H0} H1.
Step TT. (* NB: apply hoare_conseq (?) *)
- rewrite /while.entails => {H1} s h H0.
  case : H0 => H1.
  + left.
    case: H1 => x0 [x1 [H0 [H3 [x2 [H3' [H4 [H6 [H8 H9]]]]]]]].
    exists x0, x1;  Resolve_topsy.
    exists x2; by Resolve_topsy.
  + by right.
- rewrite /while.entails => s h [x0 [H4 [H5 H0]]].
  exists x0; by Resolve_topsy.

rewrite /inde => s h x0 v0 H0.
split; [intros; by Mapsto | intros; by Mapsto].

Step TT.

Step TT.

rewrite /while.entails => s h [H0 H1].
case_sepcon H0.
case : H0_h1.
- case => x0 [x1 [H4 [H9 [size'' [H10 [H11 [H12 [H13 H14]]]]]]]].
  case_sepcon H11.
  TArray_concat_split_l_l 1 H11_H02.
  case_sepcon H0.
  rewrite /= in H0_h121; case_sepcon H0_h121.
  case : H0_h121_h1211 => x3 H0_h121_h1211.
  exists (cst_e x3).
  Compose_sepcon h1211 (h122 \U h11 \U h2); first by Mapsto.
  rewrite /imp => h11' [X1 X2] h' Hh' H0.
  rewrite -!conAE.
  Compose_sepcon (h11' \U h11 \U h2) h122; last by done.
  Compose_sepcon (h11 \U h2) h11'; last by Mapsto.
  Compose_sepcon h2 h11; first by Mapsto.
  by exists x0.
- case => x0 [H9 [H10 H6]].
  exfalso.
  omegab.

Step TT.
move=> s h [H0 H2] H1.
omegab.
Qed.

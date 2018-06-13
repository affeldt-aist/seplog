(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext ssrnat_ext.
Require Import seplog integral_type.
Require Import topsy_hm topsy_hmAlloc_prg.

Require Import expr_b_dp.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.

Local Close Scope Z_scope.
Local Close Scope positive_scope.
Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.

(** Definition and Lemmas for contiguous free block *)

Fixpoint Free_block_list (l : list nat) : list (nat * bool) :=
  match l with
    | nil => nil
    | hd :: tl => (hd, true) :: Free_block_list tl
  end.

Fixpoint nat_list_sum (l : list nat) : nat :=
  match l with
    | nil => 0
    | hd :: tl => hd + nat_list_sum tl
  end.

Definition Free_block_compact_size (l : list nat) := nat_list_sum l + 2 * length l - 2.

Lemma Free_block_list_nempty : forall l, Free_block_compact_size l > 0 -> l <> nil.
Proof.
destruct l; unfold Free_block_compact_size; simpl; intros; (discriminate || omega).
Qed.

(** first execution of findFree:
  i) the heap-list is the same as in the precondition of the specification of hmAlloc
  ii) either their exists a block big enough or such a block does not exist
*)

Definition findFree_specif2 := forall adr size, size > 0 -> adr > 0 ->
  {{ fun s h => exists l1 l2 l,
    (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
    Free_block_compact_size l >= size /\
    [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
    [ var_e result ]e_s = [ null ]e_s }}
  findFree size entry fnd sz stts
  {{ fun s h => exists l1 l2 l,
    (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
    Free_block_compact_size l >= size /\
    [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
    [ var_e result ]e_s = [ null ]e_s /\
    ((exists found_free_block size'', size'' >= size /\
      In_hl (l1 ++ Free_block_list l ++ l2) (found_free_block,size'', topsy_hm.free) adr /\
      [ var_e entry ]e_s = Z_of_nat found_free_block /\
      found_free_block > 0) \/
    [ var_e entry ]e_s = [ null ]e_s) }}.

Lemma findFree_verif2 : findFree_specif2.
Proof.
rewrite /findFree_specif2 /findFree => adr size H H0.

(** entry <- var_e hmStart; *)

Step (fun s h => exists l1 l2 l,
    Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
    Free_block_compact_size l >= size /\
    [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
    [ var_e result ]e_s = [ null ]e_s /\
    [ var_e entry ]e_s = [ nat_e adr ]e_s).

case: H1 => x [x0 [x1 [H1 [H4 [H3 H6]]]]].
rewrite /wp_assign.
exists x, x0, x1.
by Resolve_topsy; rewrite eval_upd_subst.

(** stts <-* entry -.> status; *)

Step (fun s h => exists l1 l2 l,
  Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
  Free_block_compact_size l >= size /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_s = [ null ]e_s /\
  [ var_e entry ]e_s = [ nat_e adr ]e_s).

case: H1 => x [x0 [x1 [H1 [H4 [H3 [H5 H7]]]]]].
case: x H1 => [|[n b] x] H1.
- have : Free_block_compact_size x1 > 0 by ssromega.
  move/(Free_block_list_nempty x1) => H6.
  destruct x1; first by tauto.
  exists Free.
  apply mapsto_strictly_exact; split.
  + rewrite /status.
    move/(hl_getstatus nil) : H1 => H1; case_sepcon H1.
    Compose_sepcon h1 h2; [by Mapsto | done].
  + exists nil, x0, (n :: x1).
    by Resolve_topsy; rewrite eval_upd_subst.
- exists (hlstat_bool2expr b).
  apply mapsto_strictly_exact; split.
  + rewrite /status.
    move/(hl_getstatus nil) : H1 => H1; case_sepcon H1.
    Compose_sepcon h1 h2; [by Mapsto | done].
  + exists ((n, b) :: x), x0, x1.
    by Resolve_topsy; rewrite eval_upd_subst.

(** fnd <- cst_e 0%Z; *)

Step (fun s h => exists l1 l2 l,
  Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
  Free_block_compact_size l >= size /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\ [ var_e result ]e_s = [ null ]e_s /\
  [ var_e entry ]e_s = [ nat_e adr ]e_s /\ [ var_e fnd ]e_s = [ nat_e 0 ]e_s).

rewrite /wp_assign.
case : H1 => x [x0 [x1 [H1 [H4 [H3 [H5 H7]]]]]].
exists x, x0, x1; by Resolve_topsy; rewrite eval_upd_subst.

(** while ((var_e entry =/= null) &e (var_e fnd =/= cst_e 1%Z)) invariant *)

Step (fun s h => exists l1 l2 l,
  Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
  Free_block_compact_size l >= size /\
  [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\
  exists bloc_adr,
    [ var_e entry \= nat_e bloc_adr ]b_s /\
    ((bloc_adr = 0 /\ [ var_e fnd \= nat_e 0 ]b_s) \/
      (bloc_adr = get_endl (l1 ++ Free_block_list l ++ l2) adr  /\
        [ var_e fnd \= nat_e 0 ]b_s /\
        bloc_adr > 0) \/
      (exists bloc_size bloc_status,
        bloc_adr > 0 /\
        In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, bloc_status) adr /\
        [ var_e fnd \= nat_e 0 ]b_s) \/
      exists bloc_size, bloc_size >= size /\
        In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, topsy_hm.free) adr /\
        [ var_e fnd \= nat_e 1 ]b_s /\
        bloc_adr > 0)).

(** while ((var_e entry =/= null) &e (var_e fnd =/= cst_e 1%Z)) precond-str *)

rewrite /while.entails => s h [ x [x0 [x1 [H1 [H4 [H3 [H5 [H6 H8]]]]]]] ].
exists x, x0, x1; Resolve_topsy.
exists adr; Resolve_topsy.
right; right; left.
case : x H1 => [|[n b] x] H1.
- have : Free_block_compact_size x1 > 0 by ssromega.
  move/(Free_block_list_nempty x1) => H2.
  destruct x1; first by tauto.
  exists n, true.
  split; first by assumption.
  split.
  + by rewrite /= !eqxx.
  + by omegab.
- exists n, b.
  split; first by assumption.
  split.
  + by rewrite /= !eqxx.
  + by omegab.

(** while ((var_e entry <>e null) &e (var_e fnd <>e cst_e 1%Z)) precond-weak *)

rewrite /while.entails => s h [[x [x0 [x1 [H2 [H5 [H1 [H6 [x2 [H7 H8]]]]]]]]] H4].
case: H8.
- case => H9 H10.
  exists x, x0, x1; Resolve_topsy.
  by omegab.
  by omegab.
  right; subst x2; by omegab.
- case.
  + case => H11 [H3 H12].
    suff : False by done.
    rewrite /hoare_m.eval_b in H4; by omegab.
  + case.
    - case => x3 [x4 [H11 [H10 H3]]].
      suff : False by done.
      rewrite /hoare_m.eval_b in H4; by omegab.
    - case => x3 [H3 [H10 [H12 H9]]].
      exists x, x0, x1; Resolve_topsy.
      omegab.
      omegab.
      left; exists x2, x3; Resolve_topsy.
      omegab.

(** stts <-* entry -.> status; *)

Step (fun s h => exists l1 l2 l,
  Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
  Free_block_compact_size l >= size /\
  [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\
  [ var_e entry \!= null \&& var_e fnd \!= cst_e 1%Z ]b_s /\
  (exists bloc_adr,
    [ var_e entry \= nat_e bloc_adr ]b_s /\
    ((bloc_adr = get_endl (l1 ++ Free_block_list l ++ l2) adr  /\
      [ var_e fnd \= nat_e 0 ]b_s /\
      [ var_e stts \= Allocated ]b_s /\
      bloc_adr > 0) \/
    exists bloc_size bloc_status,
      bloc_adr > 0 /\
      In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, bloc_status) adr /\
      [ var_e fnd \= nat_e 0 ]b_s /\
      [ var_e stts \= hlstat_bool2expr bloc_status ]b_s))).

case: H1 => [[x [x0 [x1 [H2 [H3 [H4 [H5 [x2 [H7 H8]]]]]]]]] H9].
case: H8.
- case => H8 H10.
  suff : False by done. omegab.
- case.
  + case => H10 [H11 H12].
    exists Allocated.
    rewrite /status.
    apply mapsto_strictly_exact; split.
    * move/hl_getstat_last : H2 => H2; case_sepcon H2.
      Compose_sepcon h1 h2; [by Mapsto | done].
    * rewrite /wp_assign.
      exists x, x0, x1; Resolve_topsy.
      exists x2; Resolve_topsy.
      left; by Resolve_topsy.
  + case.
    * case => x3 [x4 [H10 [H8 H11]]].
      move/In_hl_destruct : (H8) => [x5 [x6 [H12 H13]]].
      exists (hlstat_bool2expr x4).
      apply mapsto_strictly_exact; split.
      - rewrite /status.
        rewrite H12 in H2; move/hl_getstatus : H2 => H2; case_sepcon H2.
        Compose_sepcon h1 h2; [by Mapsto | done].
      - exists x, x0, x1; Resolve_topsy.
        exists x2; Resolve_topsy.
        right; exists x3, x4; Resolve_topsy.
        by destruct x4; rewrite eval_b_upd_subst.
    * case => x3 [H8 [H10 [H11 H12]]].
      by omegab.

(** ENTRYSIZE entry sz *)

Step (fun s h => exists l1 l2 l,
  Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
  Free_block_compact_size l >= size /\
  [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\
  [ var_e entry \!= null \&& var_e fnd \!= cst_e 1%Z ]b_s /\
  (exists bloc_adr,
    [ var_e entry \= nat_e bloc_adr ]b_s /\
    ((bloc_adr = get_endl (l1 ++ Free_block_list l ++ l2) adr  /\
        [ var_e fnd \= nat_e 0 ]b_s /\
        [ var_e stts \= Allocated ]b_s /\
        [ var_e sz \= nat_e 0 ]b_s /\
        bloc_adr > 0) \/
      exists bloc_size bloc_status,
        bloc_adr > 0 /\
        In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, bloc_status) adr /\
        [ var_e fnd \= nat_e 0 ]b_s /\
        [ var_e stts \= hlstat_bool2expr bloc_status ]b_s /\
        [ var_e sz \= nat_e bloc_size ]b_s))).

unfold ENTRYSIZE.

Step (fun s h => exists l1 l2 l,
  Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
  Free_block_compact_size l >= size /\
  [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\
  [ var_e entry \!= null \&& var_e fnd \!= cst_e 1%Z ]b_s /\
  (exists bloc_adr,
    [ var_e entry \= nat_e bloc_adr ]b_s /\
    ((bloc_adr = get_endl (l1 ++ Free_block_list l ++ l2) adr  /\
      [ var_e fnd \= nat_e 0 ]b_s /\
      [ var_e stts \= Allocated ]b_s /\
      [ var_e sz \= nat_e 0 ]b_s /\
      bloc_adr > 0) \/
    exists bloc_size bloc_status,
      bloc_adr > 0 /\
      In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, bloc_status) adr /\
      [ var_e fnd \= nat_e 0 ]b_s /\
      [ var_e stts \= hlstat_bool2expr bloc_status ]b_s /\
      [ var_e sz \= nat_e (bloc_size + 2 + bloc_adr) ]b_s))).

case: H1 => [x [x0 [x1 [H1 [H3 [H2 [H5 [H4 [x2 [H7 H8]]]]]]]]]].
case: H8.
- case => H8 [H9 [H10 H11]].
  exists Allocated.
  apply mapsto_strictly_exact; split.
  + rewrite /next.
    move/hl_getnext_last : H1 => H1; case_sepcon H1.
    Compose_sepcon h1 h2; [by Mapsto | done].
  + exists x, x0, x1; Resolve_topsy.
    exists x2; Resolve_topsy.
    left; by Resolve_topsy.
- case => [x3 [x4 [H8 [H10 [H11 H9]]]]].
  exists (nat_e (x2 + 2 + x3)).
  move/In_hl_destruct : (H10) => [x5 [x6 [H12 H14]]].
  apply mapsto_strictly_exact; split.
  + rewrite /next.
    rewrite H12 in H1; move/hl_getnext : H1 => H1.
    case_sepcon H1; Compose_sepcon h1 h2; [by Mapsto | done].
  + exists x, x0, x1; Resolve_topsy.
    exists x2; Resolve_topsy.
    right; exists x3, x4; Resolve_topsy.
    rewrite eval_b_upd_subst.
    by destruct x4.

Step (fun s h => exists l1 l2 l,
  Heap_List (l1 ++ Free_block_list l ++ l2) adr s h /\
  Free_block_compact_size l >= size /\
  [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\
  [ var_e entry \!= null \&& var_e fnd \!= cst_e 1%Z ]b_s /\
  exists bloc_adr,
    [ var_e entry \= nat_e bloc_adr ]b_s /\
    ((bloc_adr = get_endl (l1 ++ Free_block_list l ++ l2) adr  /\
      [ var_e fnd \= nat_e 0 ]b_s /\
      [ var_e stts \= Allocated ]b_s /\
      [ nat_e 0 \>= var_e sz ]b_s /\
      bloc_adr > 0) \/
    exists bloc_size bloc_status,
      bloc_adr > 0 /\
      In_hl (l1 ++ Free_block_list l ++ l2) (bloc_adr, bloc_size, bloc_status) adr /\
      [ var_e fnd \= nat_e 0 ]b_s /\
      [ var_e stts \= hlstat_bool2expr bloc_status ]b_s /\
      [ var_e sz \= nat_e bloc_size ]b_s )).

case : H1 => x [x0 [x1 [H1 [H4 [H5 [H3 [H7 [x2 [H9 H8]]]]]]]]].
case : H8.
- case => [H8 [H14 [H12 [H10 H11]]]].
  rewrite /wp_assign.
  exists x, x0, x1; Resolve_topsy.
  exists x2; Resolve_topsy.
  left; by Resolve_topsy.
- case => x3 [x4 [H8 [H11 [H14 [H12 H10]]]]].
  exists x; exists x0, x1; Resolve_topsy.
  exists x2; Resolve_topsy.
  right; exists x3, x4; Resolve_topsy.
  by destruct x4; Resolve_topsy.

Step TT.
- Step TT=> s h H1.
  case : H1 => [[x [x0 [x1 [H1 [H4 [H5 [H6 [H7 [x2 [H8 H9]]]]]]]]]] H3].
  case : H9.
  + case => H9 [H15 [H13 [H11 H12]]].
    rewrite /wp_assign.
    exists x, x0, x1; Resolve_topsy.
    exists x2; Resolve_topsy.
    left; by Resolve_topsy.
  + case => x3 [x4 [H9 [H12 [H15 [H13 H11]]]]].
    rewrite /wp_assign.
    exists x, x0, x1; Resolve_topsy.
    exists x2; Resolve_topsy.
    right; exists x3, x4; by Resolve_topsy.
- Step TT.
  rewrite /while.entails => s h [[x [x0 [x1 [H1 [H4 [H5 [H6 [H7 [x2 [H8 H9]]]]]]]]]] H3].
  case : H9.
  - case => H9 [H15 [H13 [H11 H12]]].
    exists x, x0, x1; Resolve_topsy.
    exists x2; Resolve_topsy.
    left; by Resolve_topsy.
  - case => x3 [x4 [H9 [H12 [H15 [H13 H11]]]]].
    exists x, x0, x1; Resolve_topsy.
    exists x2; Resolve_topsy.
    right; by exists x3, x4.

Step TT.
- Step TT => s h H1.
  case : H1 => [[x [x0 [x1 [H1 [H4 [H5 [H6 [H7 [x2 [H8 H9]]]]]]]]]] H3].
  rewrite /wp_assign.
  exists x, x0, x1; Resolve_topsy.
  exists x2; Resolve_topsy.
  case : H9.
  + case => H9 [H16 [H14 [H12 H13]]].
    right; left.
    rewrite /Allocated in H14.
    suff : False by done. omegab.
  + case => x3 [x4 [H9 [H13 [H16 [H14 H12]]]]].
    right; right; right; exists x3; split.
    by omegab.
    Resolve_topsy.
    destruct x4; first by done.
    suff : False by done. omegab.

Step TT.
rewrite /while.entails => s h [[x [x0 [x1 [H2 [H5 [H7 [h6 [H9 [x2 [H4 H8]]]]]]]]]] H10].
case : H8.
- case => H11 [H12 [H13 [H14 H15]]].
  exists (nat_e 0).
  rewrite /next.
  apply mapsto_strictly_exact; split.
  move/hl_getnext_last : H2 => H2; case_sepcon H2.
  Compose_sepcon h1 h2; [by Mapsto | done].
  exists x, x0, x1; Resolve_topsy.
  exists 0; Resolve_topsy.
  left; by Resolve_topsy.
- case => x3 [x4 [H11 [H8 [H12 [H13 H14]]]]].
  exists (nat_e (x2 + 2 + x3)).
  move/In_hl_destruct : H8 => [x5 [x6 [H16 H17]]].
  rewrite H16 in H2.
  apply mapsto_strictly_exact; split.
  + rewrite /next.
    move/hl_getnext : H2 => H18.
    case_sepcon H18; Compose_sepcon h1 h2; [by Mapsto | done].
  + exists x, x0, x1.
    rewrite H16.
    Resolve_topsy.
    exists (x2 + 2 + x3); Resolve_topsy.
    case : x6 H2 H16 => [|[n b] x6] H2 H16.
    * right; left; Resolve_topsy.
      rewrite get_endl_app /=; ssromega.
      ssromega.
    * right; right; left; exists n, b.
      split; first by ssromega.
      split; last by Resolve_topsy.
      apply In_hl_or_app; right => /=.
      case: ifP => [_ //| _].
      by rewrite H17 !eqxx.
Qed.

(** we perform a compaction => we now for sure that a big enough free block for the allocation exists *)
Definition compact_specif2 := forall adr size, size > 0 -> adr > 0 ->
  {{fun s h => exists l1 l2 l,
    (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
    (Free_block_compact_size l) >= size /\
    [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
    [ var_e result ]e_s = [ null ]e_s /\
    [ var_e cptr ]e_s = [ nat_e adr ]e_s }}
  compact cptr nptr stts
  {{ fun s h => exists l,
    (Heap_List l adr) s h /\
    [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
    [ var_e result ]e_s = [ null ]e_ s /\
    exists free_adr free_size, free_size >= size /\
      In_hl l (free_adr, free_size, topsy_hm.free) adr }}.

Lemma compact_verif2 : compact_specif2.
Proof.
rewrite /compact_specif2 /compact => adr size H H0.

(** First loop invariant *)

Step (fun s h => [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_s = [ null ]e_s /\
  exists cur_adr, [ var_e cptr ]e_s = [ nat_e cur_adr ]e_ s /\
    (exists l1 l l2 free_size,
      Heap_List (l1 ++ (free_size, topsy_hm.free) :: (Free_block_list l) ++ l2) adr s h /\
      Free_block_compact_size (free_size :: l) >= size /\
      ((cur_adr > 0 /\ exists cur_size cur_status,
          In_hl l1 (cur_adr, cur_size, cur_status) adr) \/
      (cur_adr > 0 /\ cur_adr = get_endl l1 adr) \/
      (cur_adr > 0 /\ l = nil /\
        exists cur_size cur_status,
          In_hl l2 (cur_adr, cur_size, cur_status) (get_endl (l1 ++ (free_size,topsy_hm.free) :: nil) adr)) \/
      (cur_adr > 0 /\ l = nil /\
        cur_adr = get_endl (l1 ++ (free_size, topsy_hm.free) :: l2) adr) \/
        (l = nil /\ cur_adr = 0)))).

(** First loop invariant PS *)

rewrite /while.entails => s h [x [x0 [x1 [H1 [H4 [H3 [H5 H7]]]]]]].
Resolve_topsy.
exists adr; Resolve_topsy.
lapply (Free_block_list_nempty x1); [intros | ssromega].
destruct x1; try tauto.
exists x, x1, x0, n; Resolve_topsy.
case : x H1 => [| [n0 b] x] H1.
- right; by left.
- left; Resolve_topsy.
  exists n0, b; by rewrite /= !eqxx.

(** First loop QW *)

rewrite /while.entails => s h [[H4 [H2 [x [H5 [x0 [x1 [x2 [x3 [H1 [H8 H9]]]]]]]]]] H3].
exists (x0 ++ (x3, topsy_hm.free) :: Free_block_list x1 ++ x2).
repeat (split => //).
case: H9.
- case => H7 [x4 [x5 H9]].
  suff : False by done.
  rewrite /hoare_m.eval_b in H3; by omegab. (* TODO *)
case.
- case => H6 H9.
  suff : False by done.
  rewrite /hoare_m.eval_b in H3; by omegab.
- case.
  case => H7 [H10 [x4 [x5 H9]]].
  suff : False by done.
  rewrite /hoare_m.eval_b in H3; by omegab.
- case.
  case => H6 [H10 H11].
  suff : False by done.
  rewrite /hoare_m.eval_b in H3; by omegab.
- case => H6 _.
  exists (get_endl x0 adr), x3.
  split.
  - rewrite H6 /Free_block_compact_size /= in H8; ssromega.
  - apply In_hl_or_app; right => /=.
    by rewrite !eqxx.

(** stts <-* cptr -.> status;  *)

Step (fun s h => [ var_e hmStart ]e_s = [ nat_e adr ]e_ s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  exists cur_adr, [ var_e cptr ]e_ s = [ nat_e cur_adr ]e_ s /\
    (exists l1 l l2 free_size,
      Heap_List (l1 ++ (free_size, topsy_hm.free) :: (Free_block_list l) ++ l2) adr s h /\
      Free_block_compact_size (free_size :: l) >= size /\
      ((cur_adr > 0 /\
        exists cur_size cur_status,
          In_hl l1 (cur_adr, cur_size, cur_status) adr /\
          [ var_e stts \= hlstat_bool2expr cur_status ]b_s
      ) \/
      (cur_adr > 0 /\ cur_adr = get_endl l1 adr /\
        [ var_e stts \= hlstat_bool2expr topsy_hm.free ]b_s
      ) \/
      (cur_adr > 0 /\ l = nil /\
        exists cur_size cur_status,
          In_hl l2 (cur_adr, cur_size, cur_status) (get_endl (l1++(free_size,topsy_hm.free)::nil) adr) /\
          [ var_e stts \= hlstat_bool2expr cur_status ]b_s
      ) \/
      (cur_adr > 0 /\ l = nil /\
        cur_adr = (get_endl (l1 ++ (free_size, topsy_hm.free) :: l2) adr) /\
        [ var_e stts \= hlstat_bool2expr alloc ]b_s)))).

case: H1 => [[H4 [H2 [x [H5 [x0 [x1 [x2 [x3 [H3 [H8 H9]]]]]]]]]] H1].
case : H9.
- case => [H7 [x4 [x5 H9]]].
  exists (hlstat_bool2expr x5).
  unfold status.
  apply mapsto_strictly_exact; split.
  move/In_hl_destruct : H9 => [x6 [x7 [H11 H12]]].
  rewrite H11 in H3; Hl_getstatus H3 x4 H6; [by Mapsto | done].
  rewrite /wp_assign.
  split; first by rewrite eval_upd_subst.
  split.
  by rewrite eval_upd_subst.
  exists x; Resolve_topsy.
  by rewrite eval_upd_subst.
  exists x0, x1, x2, x3; Resolve_topsy.
  left; Resolve_topsy.
  exists x4, x5; Resolve_topsy.
  by destruct x5; rewrite eval_b_upd_subst.
- case.
  + case => H6 H9.
    exists (hlstat_bool2expr topsy_hm.free).
    unfold status.
    apply mapsto_strictly_exact; split.
    Hl_getstatus H1 x3 H7; [by Mapsto | done].
    rewrite /wp_assign.
    split; first by rewrite eval_upd_subst.
    split; first by rewrite eval_upd_subst.
    exists x; Resolve_topsy.
    by rewrite eval_upd_subst.
    exists x0, x1, x2, x3; Resolve_topsy.
    right; left; by Resolve_topsy.
  + case.
    * case => [H7 [H10 [x4 [x5 H9]]]].
      exists (hlstat_bool2expr x5).
      rewrite /status.
      apply mapsto_strictly_exact; split.
      move/In_hl_destruct : (H9) => [x6 [x7 [H12 H13]]].
      rewrite H12 in H3; Hl_getstatus H3 x4 H6; last by done.
      subst x1.
      rewrite [Free_block_list _]/= in H6_h1.
      rewrite !get_endl_app /= in H13 H6_h1.
      by Mapsto.
      split; first by rewrite eval_upd_subst.
      split; first by rewrite eval_upd_subst.
      exists x; Resolve_topsy.
      by rewrite eval_upd_subst.
      exists x0, x1, x2, x3; Resolve_topsy.
      right; right; left; Resolve_topsy.
      exists x4, x5; Resolve_topsy.
      by destruct x5; rewrite eval_b_upd_subst.
    * case.
      - case => [H6 [H10 H11]].
        subst x1.
        exists (hlstat_bool2expr alloc).
        rewrite /status.
        apply mapsto_strictly_exact; split.
        move/hl_getstat_last : H3 => H3; case_sepcon H3.
        Compose_sepcon h1 h2; [by Mapsto | done].
        split; first by rewrite eval_upd_subst.
        split; first by rewrite eval_upd_subst.
        exists x; Resolve_topsy.
        by rewrite eval_upd_subst.
        exists x0, nil, x2, x3; Resolve_topsy.
        right; right; right; by Resolve_topsy.
      - case => _ H7.
        suff : False by done. omegab.

(** (ifte var_e stts \= Free) Post condition  *)

Step (fun s h => [ var_e hmStart ]e_s = [ nat_e adr ]e_ s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  exists cur_adr, [ var_e cptr ]e_ s = [ nat_e cur_adr ]e_ s /\
    ((exists l1 l l2 free_size,
      Heap_List (l1 ++ (free_size, topsy_hm.free) :: (Free_block_list l) ++ l2) adr s h /\
      Free_block_compact_size (free_size :: l) >= size /\
      ((cur_adr > 0 /\
          exists cur_size cur_status,
              In_hl l1 (cur_adr, cur_size, cur_status) adr) \/
        (cur_adr > 0 /\ cur_adr = get_endl l1 adr /\ l = nil) \/
        (cur_adr > 0 /\ l = nil /\
          exists cur_size cur_status,
              In_hl l2 (cur_adr, cur_size, cur_status) (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr)) \/
        (cur_adr > 0 /\ l = nil /\
          cur_adr = get_endl (l1 ++ (free_size,topsy_hm.free) :: l2) adr))))).

(** nptr <-* cptr -.> next; *)

Step (fun s h => [ var_e hmStart ]e_ s = [ nat_e adr ]e_ s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  exists cur_adr, [ var_e cptr ]e_ s = [ nat_e cur_adr ]e_ s /\
    exists l1 l l2 free_size,
      Heap_List (l1 ++ (free_size, topsy_hm.free) :: (Free_block_list l) ++ l2) adr s h /\
      Free_block_compact_size (free_size :: l) >= size /\
      ((cur_adr > 0 /\
          exists cur_size,
            In_hl l1 (cur_adr, cur_size, topsy_hm.free) adr /\
            [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s) \/
        (cur_adr > 0 /\ cur_adr = get_endl l1 adr /\
          [ var_e nptr \= nat_e (cur_adr + 2 + free_size) ]b_s) \/
        (l = nil /\ cur_adr > 0 /\
          exists cur_size,
            In_hl l2 (cur_adr, cur_size, topsy_hm.free) (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
            [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s))).

case : H1 => [[H4 [H2 [x [H5 [x0 [x1 [x2 [x3 [H1 [H8 H9]]]]]]]]]] H3].
case : H9.
- case => H7 [x4 [x5 [H6 H10]]].
  unfold next.
  exists (nat_e (x + 2 + x4)).
  apply mapsto_strictly_exact; split.
  move/In_hl_destruct : H6 => [x6 [x7 [H12 H6]]].
  rewrite H12 in H1; Hl_getnext H1 x4 H9; [by Mapsto | done].
  split; first by rewrite eval_upd_subst.
  split; first by rewrite eval_upd_subst.
  exists x; Resolve_topsy.
  by rewrite eval_upd_subst.
  exists x0, x1, x2, x3; Resolve_topsy.
  left; Resolve_topsy.
  exists x4; Resolve_topsy.
  destruct x5 => //.
  suff : False by done. omegab.
- case.
  + case => H6 [H10 H11].
    unfold next.
    exists (nat_e (x + 2 + x3)).
    apply mapsto_strictly_exact; split.
    Hl_getnext H1 x3 H7; [by Mapsto | done].
    split; first by rewrite eval_upd_subst.
    split; first by rewrite eval_upd_subst.
    exists x; Resolve_topsy.
    by rewrite eval_upd_subst.
    exists x0, x1, x2, x3; Resolve_topsy.
    right; left; by Resolve_topsy.
  + case.
    * case => H7 [H10 [x4 [x5 [H6 H11]]]].
      unfold next.
      exists (nat_e (x + 2 + x4)).
      apply mapsto_strictly_exact; split.
      subst x1; simpl Free_block_list in H1.
      move/In_hl_destruct : H6 => [x1 [x6 [H12 H6]]].
      rewrite H12 in H1; Hl_getnext H1 x4 H9; last by done.
      rewrite get_endl_app /= in H6.
      rewrite !get_endl_app /= H6 in H9_h1; by Mapsto.
      split; first by rewrite eval_upd_subst.
      split; first by rewrite eval_upd_subst.
      exists x; Resolve_topsy.
      by rewrite eval_upd_subst.
      exists x0, x1, x2, x3; Resolve_topsy.
      right; right; Resolve_topsy.
      exists x4; Resolve_topsy.
      destruct x5 => //.
      suff : False by done. omegab.
    * case => H7 [H10 [H9 H12]].
      suff : False by done. omegab.

(** stts <-* nptr -.> status; *)

Step (fun s h => [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_s = [ null ]e_s /\
  exists cur_adr, [ var_e cptr ]e_s = [ nat_e cur_adr ]e_s /\
    exists l1 l l2 free_size,
      Heap_List (l1 ++ (free_size, topsy_hm.free) :: Free_block_list l ++ l2) adr s h /\
      Free_block_compact_size (free_size :: l) >= size /\
      ((cur_adr > 0 /\ exists cur_size,
        In_hl l1 (cur_adr, cur_size, topsy_hm.free) adr /\
        [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s /\
        ((exists next_status next_size,
          In_hl l1 (cur_adr + 2 + cur_size, next_size, next_status) adr /\
          [ var_e stts \= (hlstat_bool2expr next_status) ]b_s) \/
        (cur_adr + 2 + cur_size = get_endl l1 adr /\
          [ var_e stts \= (hlstat_bool2expr topsy_hm.free) ]b_s))) \/
      (cur_adr = get_endl l1 adr /\ cur_adr > 0 /\
        [ var_e nptr \= nat_e (cur_adr + 2 + free_size) ]b_s /\
        ((l = nil /\ exists next_status next_size,
          In_hl l2 (cur_adr + 2 + free_size, next_size, next_status)
            (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
          [ var_e stts \= (hlstat_bool2expr next_status) ]b_s) \/
        (l <> nil /\ exists hd tl,
          l = hd :: tl /\
          [ var_e stts \= hlstat_bool2expr topsy_hm.free ]b_s) \/
        (l = nil /\
          cur_adr + 2 + free_size = get_endl
          (l1 ++ (free_size, topsy_hm.free) :: nil) adr /\
          [ var_e stts \= hlstat_bool2expr alloc ]b_s))) \/
      (l = nil /\ cur_adr > 0 /\
        exists cur_size,
          In_hl l2 (cur_adr, cur_size, topsy_hm.free)
            (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
          [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s /\
          ((exists next_status next_size,
            In_hl l2 (cur_adr + 2 + cur_size, next_size, next_status)
              (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
            [ var_e stts \= hlstat_bool2expr next_status ]b_s) \/
          (cur_adr + 2 + cur_size = get_endl (l1 ++ (free_size, topsy_hm.free) :: l2) adr /\
            [ var_e stts \= hlstat_bool2expr alloc ]b_s))))).

(** L *)

case : H1 => [H2 [H4 [x [H3 [x0 [x1 [x2 [x3 [H1 [H7 H8]]]]]]]]]].
rewrite /status.
case: H8.
- case => H6 [x4 [H8 H9]].
  move/In_hl_destruct : (H8) => [x5 [x6 [H10 H11 ]]].
  case : x6 H10 => [|[n b] x6] H10.
  + exists (hlstat_bool2expr topsy_hm.free).
    apply mapsto_strictly_exact; split.
    * Hl_getstatus H1 x3 H5; last by done.
      rewrite H10 get_endl_app /= H11 in H5_h1; by Mapsto.
    * rewrite /wp_assign.
      Resolve_topsy.
      by rewrite eval_upd_subst.
      by rewrite eval_upd_subst.
      exists x; Resolve_topsy.
      by rewrite eval_upd_subst.
      exists x5, (x3 :: x1), x2, x4.
      split.
      set t := _ ++ _.
      rewrite (_ : x0 ++ _ = t) in H1; last first.
        rewrite H10 /t; by List_eq.
      by Resolve_topsy.
      Resolve_topsy.
      - rewrite /Free_block_compact_size /= in H7 *; ssromega.
      - right; left; Resolve_topsy.
        right; left; Resolve_topsy.
        + done.
        + exists x3, x1; by Resolve_topsy.
  + exists (hlstat_bool2expr b).
    apply mapsto_strictly_exact; split.
    * rewrite H10 in H1.
      Hl_getstatus H1 n H5; last by done.
      rewrite get_endl_app /= H11 in H5_h1; by Mapsto.
    * rewrite /wp_assign.
      Resolve_topsy.
      by rewrite eval_upd_subst.
      by rewrite eval_upd_subst.
    * exists x.
      Resolve_topsy.
      by rewrite eval_upd_subst.
      exists x0, x1, x2, x3; Resolve_topsy.
      left; Resolve_topsy.
      exists x4; Resolve_topsy.
      left.
      exists b, n; Resolve_topsy.
      rewrite H10; apply In_hl_or_app; right => /=.
      set t' := _ && _.
      destruct t' => //.
      by rewrite H11 !eqxx.
      by destruct b; rewrite eval_b_upd_subst.
- case => H6.
  + case: H6 => H5 [H9 H10].
    destruct x1.
    * simpl in H1.
      case : x2 H1 => [|[n b] x2] H1.
      - exists (hlstat_bool2expr alloc).
        apply mapsto_strictly_exact; split.
        + move/hl_getstat_last : H1 => H1; case_sepcon H1.
          Compose_sepcon h1 h2; last by done.
          rewrite get_endl_app /= -H9 in H1_h1; by Mapsto.
        + rewrite /wp_assign.
          Resolve_topsy.
          by rewrite eval_upd_subst.
          by rewrite eval_upd_subst.
          exists x; Resolve_topsy.
          by rewrite eval_upd_subst.
          exists x0, nil, nil, x3; Resolve_topsy.
          right; left; Resolve_topsy.
          right; right; Resolve_topsy.
          by rewrite get_endl_app /= -H9.
      - exists (hlstat_bool2expr b).
        apply mapsto_strictly_exact; split.
        + Hl_getstatus H1 n H6; last by done.
          rewrite get_endl_app /= -H9 in H6_h1; by Mapsto.
        + rewrite /wp_assign.
          Resolve_topsy.
          by rewrite eval_upd_subst.
          by rewrite eval_upd_subst.
          exists x;  Resolve_topsy.
          by rewrite eval_upd_subst.
          exists x0, nil, ((n, b) :: x2), x3; Resolve_topsy.
          right; left; Resolve_topsy.
          left; Resolve_topsy.
          exists b, n; Resolve_topsy.
          by rewrite /= get_endl_app /= H9 !eqxx.
          by destruct b; rewrite eval_b_upd_subst.
    * simpl in H1.
      exists (hlstat_bool2expr topsy_hm.free).
      apply mapsto_strictly_exact; split.
      - Hl_getstatus H1 n H6; last by done.
        rewrite get_endl_app /= -H9 in H6_h1; by Mapsto.
      - rewrite /wp_assign.
        Resolve_topsy.
        by rewrite eval_upd_subst.
        by rewrite eval_upd_subst.
        exists x; Resolve_topsy.
        by rewrite eval_upd_subst.
        exists x0, (n :: x1), x2, x3; Resolve_topsy.
        right; left; Resolve_topsy.
        right; left; Resolve_topsy.
        done.
        exists n, x1; by Resolve_topsy.
  + case : H6 => H5 [H9 [x4 [H8 H10]]].
    subst x1; simpl in H1.
    move/In_hl_destruct : (H8) => [x1 [x5 [H11 H12]]].
    case : x5 H11 => [|[n b] x5] H11.
    * exists (hlstat_bool2expr alloc).
      apply mapsto_strictly_exact; split.
      - move/hl_getstat_last : H1 => H1; case_sepcon H1.
        Compose_sepcon h1 h2; last by done.
        rewrite !get_endl_app /= in H12.
        rewrite !get_endl_app /= H11 !get_endl_app /= H12 in H1_h1; by Mapsto.
      - split; first by rewrite eval_upd_subst.
        split; first by rewrite eval_upd_subst.
        exists x; Resolve_topsy.
        by rewrite eval_upd_subst.
        exists x0, nil, x2, x3; Resolve_topsy.
        right; right; Resolve_topsy.
        exists x4; Resolve_topsy.
        right; split.
        by rewrite -H12 !get_endl_app /= H11 get_endl_app.
        by rewrite eval_b_upd_subst.
    * exists (hlstat_bool2expr b).
      apply mapsto_strictly_exact; split.
      rewrite H11 in H1; Hl_getstatus H1 n H5; last by done.
      rewrite get_endl_app /= in H12.
      rewrite get_endl_app /= get_endl_app /= H12 /= in H5_h1; by Mapsto.
      split; first by rewrite eval_upd_subst.
      split; first by rewrite eval_upd_subst.
      exists x; Resolve_topsy.
      by rewrite eval_upd_subst.
      exists x0, nil, x2, x3; Resolve_topsy.
      right; right; Resolve_topsy.
      exists x4; Resolve_topsy.
      left; exists b, n; split.
      rewrite H11; apply In_hl_or_app; right => /=.
      set t' := _ && _.
      destruct t' => //.
      by rewrite H12 !eqxx.
      by destruct b; rewrite eval_b_upd_subst.

(** Second loop invariant *)

Step (fun s h => [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  exists cur_adr, [ var_e cptr ]e_ s = [ nat_e cur_adr ]e_ s /\
    (exists l1 l l2 free_size,
      Heap_List (l1 ++ (free_size,topsy_hm.free)::(Free_block_list l) ++ l2) adr s h /\
      Free_block_compact_size (free_size::l) >= size /\
      ((cur_adr > 0 /\
          exists cur_size,
            In_hl l1 (cur_adr, cur_size, topsy_hm.free) adr /\
            [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s /\
            ((exists next_status next_size,
                  In_hl l1 (cur_adr + 2 + cur_size, next_size, next_status) adr /\
                  [ var_e stts \= hlstat_bool2expr next_status ]b_s
              ) \/
              (cur_adr + 2 + cur_size = get_endl l1 adr /\
                [ var_e stts \= hlstat_bool2expr topsy_hm.free ]b_s))) \/
        (cur_adr = get_endl l1 adr /\ cur_adr > 0 /\
          [ var_e nptr \= nat_e (cur_adr + 2 + free_size) ]b_s /\
          ((l = nil /\ exists next_status next_size,
            In_hl l2 (cur_adr + 2 + free_size, next_size, next_status) (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
            [ var_e stts \= hlstat_bool2expr next_status ]b_s
            ) \/
            (l <> nil /\
              exists hd tl, l = hd :: tl (*TODO: simplify*) /\
                [ var_e stts \= hlstat_bool2expr topsy_hm.free ]b_s
            )  \/
            (l = nil /\
              cur_adr + 2 + free_size = get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr /\
              [ var_e stts \= hlstat_bool2expr alloc ]b_s))) \/
        (l = nil /\ cur_adr > 0 /\
          exists cur_size,
            In_hl l2 (cur_adr, cur_size, topsy_hm.free) (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
            [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s /\
            ((exists next_status next_size,
              In_hl l2 (cur_adr + 2 + cur_size, next_size, next_status) (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
              [ var_e stts \= hlstat_bool2expr next_status ]b_s) \/
            (cur_adr + 2 + cur_size = get_endl (l1 ++ (free_size, topsy_hm.free) :: l2) adr /\
              [ var_e stts \= hlstat_bool2expr alloc ]b_s)))))).

(** Second loop PS *)

rewrite /while.entails => s h [X2 [H4 [x [H3 [x0 [x1 [x2 [x3 [H1 [H7 H8]]]]]]]]]].
Resolve_topsy.
exists x; Resolve_topsy.
exists x0, x1, x2, x3; by Resolve_topsy.

(** Second loop QW *)

rewrite /while.entails => s h [[X2 [H4 [x [H2 [x0 [x1 [x2 [x3 [H1 [H7 H8]]]]]]]]]] H3].
Resolve_topsy.
exists x; Resolve_topsy.
exists x0, x1, x2, x3; Resolve_topsy.
case: H8.
- case=> x_gt_0 [x4 [H9 [H12 H11]]].
  case: H11.
  + case => x5 [x6 [H10 H13]].
    left; Resolve_topsy.
    exists x4, topsy_hm.free; by Resolve_topsy.
  + case => H10 /= H13.
    by rewrite /hoare_m.eval_b /= H13 in H3.
- case.
  + case=> H6 [H10 [H9 H12]].
    case : H12.
    * case=> H11 [x4 [x5 [In_hl_x2 H13]]].
      right; left; by Resolve_topsy.
    * case.
      - case=> Hx1 [x4 [x5 [H11 /= H13]]].
        by rewrite /hoare_m.eval_b /= H13 in H3.
      - case=> x1_nil [H13 H14].
        right; left; by Resolve_topsy.
  + case=> H6 [H10 [x4 [H9 [H14 H12]]]].
    case: H12 => [| _].
    * case => x5 [x6 [H11 H12]].
      right; right; left; Resolve_topsy.
      exists x4, topsy_hm.free; by Resolve_topsy.
    * right; right; left; Resolve_topsy.
      by exists x4, topsy_hm.free; Resolve_topsy.

(** stts <-* nptr -.> next; *)

Step (fun s h => [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
    [ var_e result ]e_s = [ null ]e_ s /\
    exists cur_adr, [ var_e cptr ]e_ s = [ nat_e cur_adr ]e_ s /\
      exists l1 l l2 free_size,
        Heap_List (l1 ++ (free_size, topsy_hm.free) :: (Free_block_list l) ++ l2) adr s h /\
        Free_block_compact_size (free_size::l) >= size /\
        ((cur_adr > 0 /\
          exists cur_size,
            In_hl l1 (cur_adr, cur_size, topsy_hm.free) adr /\
            [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s /\
            ( (exists next_size,
              In_hl l1 (cur_adr + 2 + cur_size, next_size, topsy_hm.free) adr /\
              [ var_e stts \= nat_e (cur_adr + 2 + cur_size + 2 + next_size) ]b_s
            ) \/
            (cur_adr + 2 + cur_size = get_endl l1 adr /\
              [ var_e stts \= nat_e (cur_adr + 2 + cur_size + 2 + free_size) ]b_s
            ))) \/
        (cur_adr = get_endl l1 adr /\ cur_adr > 0 /\
          [ var_e nptr \= nat_e (cur_adr + 2 + free_size) ]b_s /\
          ((l = nil /\
            exists next_size,
              In_hl l2 (cur_adr + 2 + free_size, next_size, topsy_hm.free) (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
              [ var_e stts \= nat_e (cur_adr + 2 + free_size + 2 + next_size) ]b_s) \/
            (l <> nil /\ exists hd tl,
              l = hd :: tl /\ (*TODO: simplify*)
              [ var_e stts \= nat_e (cur_adr + 2 + free_size + 2 + hd) ]b_s))) \/
        (l = nil /\ cur_adr > 0 /\
          exists cur_size,
            In_hl l2 (cur_adr, cur_size, topsy_hm.free) (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
            [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s /\
            exists next_size,
              In_hl l2 (cur_adr + 2 + cur_size, next_size, topsy_hm.free)
              (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
              [ var_e stts \= nat_e (cur_adr + 2 + cur_size + 2 + next_size)]b_s))).

case : H1 => [[H4 [H2 [x [H5 [x0 [x1 [x2 [x3 [H1 [H8 H9]]]]]]]]]] H3].
unfold next.
case : H9.
- case  => H7 [x4 [H9 [H11 H12]]].
  case : H12.
  + case => x5 [x6 [H10 H12]].
    exists (nat_e (x + 2 + x4 + 2 + x6)).
    apply mapsto_strictly_exact; split.
    move/In_hl_destruct : H10 => [x7 [x8 [H13 H14]]].
    rewrite H13 in H1; Hl_getnext H1 x6 H6; [by Mapsto | done].
    split; first by rewrite eval_upd_subst.
    split; first by rewrite eval_upd_subst.
    exists x; Resolve_topsy.
    by rewrite eval_upd_subst.
    exists x0, x1, x2, x3; Resolve_topsy.
    left; Resolve_topsy.
    exists x4; Resolve_topsy.
    left; exists x6; Resolve_topsy.
    destruct x5 => //.
    suff : False by done. omegab.
  + case => H10 H12.
    exists (nat_e (x + 2 + x4 + 2 + x3)).
    apply mapsto_strictly_exact; split.
    Hl_getnext H1 x3 H6; [by Mapsto | done].
    split; first by rewrite eval_upd_subst.
    split; first by rewrite eval_upd_subst.
    exists x; Resolve_topsy.
    by rewrite eval_upd_subst.
    exists x0, x1, x2, x3; Resolve_topsy.
    left; Resolve_topsy.
    exists x4; Resolve_topsy.
    right; by Resolve_topsy.
- case.
  + case => H6 [H10 [H9 H12]].
    case : H12.
    * case => H11 [x4 [x5 [H7 H13]]].
      exists (nat_e (x + 2 + x3 + 2 + x5)).
      apply mapsto_strictly_exact; split.
      move/In_hl_destruct : H7 => [x6 [x7 [H14 H15]]].
      rewrite H14 in H1; Hl_getnext H1 x5 H7; last by done.
      subst x1; rewrite /Free_block_list !get_endl_app /= in H7_h1.
      rewrite !get_endl_app /= in H15; by Mapsto.
      split; first by rewrite eval_upd_subst.
      split; first by rewrite eval_upd_subst.
      exists x; Resolve_topsy.
      by rewrite eval_upd_subst.
      exists x0, x1, x2, x3; Resolve_topsy.
      right; left; Resolve_topsy.
      left; Resolve_topsy.
      exists x5; Resolve_topsy.
      destruct x4 => //.
      suff : False by done. omegab.
    * case.
      - case => H7 [x4 [x5 [H11 H13]]].
        exists (nat_e (x + 2 + x3 + 2 + x4)).
        apply mapsto_strictly_exact; split.
        rewrite H11 /= in H1; Hl_getnext H1 x4 H12; last by done.
        rewrite get_endl_app /= -H6 in H12_h1; by Mapsto.
        rewrite /wp_assign.
        Resolve_topsy; rewrite eval_upd_subst //.
        exists x; Resolve_topsy.
        exists x0, x1, x2, x3; Resolve_topsy.
        right; left; Resolve_topsy.
        right; Resolve_topsy.
        exists x4, x5; by Resolve_topsy.
      - case => H7 [H13 H14].
        suff : False by done. omegab.
  + case => H6 [H10 [x4 [H9 [H12 H13]]]].
    case : H13.
    * case => x5 [x6 [H11 H13]].
      exists (nat_e (x + 2 + x4 + 2 + x6)).
      apply mapsto_strictly_exact; split.
      rewrite /= in H1.
      subst x1.
      rewrite !get_endl_app /= in H11; move/In_hl_destruct : H11 => [x1 [x7 [H14 H15]]].
      rewrite H14 in H1; Hl_getnext H1 x6 H6; last by done.
      rewrite !get_endl_app /= in H6_h1; by Mapsto.
      rewrite /wp_assign.
      Resolve_topsy; rewrite eval_upd_subst //.
      exists x; Resolve_topsy.
      exists x0, x1, x2, x3; Resolve_topsy.
      right; right; Resolve_topsy.
      exists x4; Resolve_topsy.
      exists x6; Resolve_topsy.
      destruct x5 => //.
      suff : False by done. omegab.
    * case => H11 H13.
      suff : False by done. omegab.

(** cptr -.> next *<- var_e stts;*)

Step (fun s h => [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_ s = [ null ]e_s /\
  exists cur_adr, [ var_e cptr ]e_s = [ nat_e cur_adr ]e_ s /\
    (exists l1 l l2 free_size,
      Heap_List (l1 ++ (free_size, topsy_hm.free) :: (Free_block_list l) ++ l2) adr s h /\
      Free_block_compact_size (free_size :: l) >= size /\
      ((cur_adr > 0 /\ exists cur_size,
            In_hl l1 (cur_adr, cur_size, topsy_hm.free) adr /\
            [ var_e stts \= nat_e (cur_adr + 2 + cur_size) ]b_s) \/
        (cur_adr > 0 /\ cur_adr = get_endl l1 adr /\
          [ var_e stts \= nat_e (cur_adr + 2 + free_size) ]b_s) \/
        (l = nil /\ cur_adr > 0 /\
          exists cur_size,
            In_hl l2 (cur_adr, cur_size, topsy_hm.free) (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
            [ var_e stts \= nat_e (cur_adr + 2 + cur_size) ]b_s)))).

unfold next.
case : H1 => [H2 [H4 [x [H3 [x0 [x1 [x2 [x3 [H1 [H7 H8]]]]]]]]]].
case : H8.
- case => H6 [x4 [H8 [H10 H11]]].
  case : H11.
  + case => x5 [H5 H11].
    case: (In_hl_next _ _ _ _ _ _ _ H8 H5) => x6 [x7 [H9 H13]].
    rewrite H9 -catA in H1.
    case/Heap_List_compaction : H1 => x8 H12.
    case_sepcon H12.
    exists x8; Compose_sepcon h1 h2.
    by Mapsto.
    move: H12_h2; apply monotony_imp => h'' H14; first by Mapsto.
    Resolve_topsy.
    exists x; Resolve_topsy.
    exists (x6 ++ (x4 + x5 + 2, topsy_hm.free) :: x7), x1, x2, x3; Resolve_topsy.
    by rewrite -!catA.
    left; Resolve_topsy.
    exists (x4 + x5 + 2); Resolve_topsy.
    apply In_hl_or_app; right; by rewrite /= -H13 !eqxx.
  + case => H9 H11.
    case : (In_hl_last _ _ _ _ _ H8 (sym_eq H9)) => x5 H5.
    subst x0.
    rewrite -catA in H1.
    case/Heap_List_compaction : H1 => x0 H5.
    case_sepcon H5.
    exists x0.
    Compose_sepcon h1 h2.
    rewrite get_endl_app /= in H9; by Mapsto.
    move: H5_h2; apply monotony_imp => h' Hh'.
    rewrite get_endl_app /= in H9; by Mapsto.
    Resolve_topsy.
    exists x; Resolve_topsy.
    exists x5, x1, x2, (x4 + x3 + 2); Resolve_topsy.
    rewrite /Free_block_compact_size /= in H7 *; ssromega.
    right; left; Resolve_topsy.
    rewrite get_endl_app /= in H9; ssromega.
- case.
  + case => H5 [H9 [H8 H11]].
    case : H11.
    * case => H10 [x4 [H11 H12]].
      rewrite get_endl_app /= -H5 in H11; case/In_hl_first : H11 => x5 H13.
      subst x2 x1.
      rewrite /= ( _ : x0 ++ (x3, topsy_hm.free) :: (x4, topsy_hm.free) :: x5 =
        x0 ++ (x3, topsy_hm.free) :: (x4, topsy_hm.free) :: nil ++ x5) // in H1.
      case/Heap_List_compaction : H1 => x1 H10.
      case_sepcon H10.
      exists x1.
      Compose_sepcon h1 h2; first by Mapsto.
      move: H10_h2; apply monotony_imp => h'' H10; first by Mapsto.
      Resolve_topsy.
      exists x; Resolve_topsy.
      exists x0, nil, x5, (x3 + x4 + 2); Resolve_topsy.
      rewrite /Free_block_compact_size /= in H7 *; ssromega.
      right; left; by Resolve_topsy.
    * case => H10 [x4 [x5 [H6 H12]]].
      subst x1; clear H10.
      rewrite /= ( _ : x0 ++ (x3, topsy_hm.free) :: (x4, true) :: Free_block_list x5 ++ x2 =
        x0 ++ (x3, topsy_hm.free) :: (x4, true) :: nil ++ Free_block_list x5 ++ x2) // in H1.
      case/Heap_List_compaction : H1 => x1 H6.
      case_sepcon H6.
      exists x1; Compose_sepcon h1 h2.
      by Mapsto.
      move: H6_h2; apply monotony_imp => h'' H10; first by Mapsto.
      Resolve_topsy.
      exists x; Resolve_topsy.
      exists x0, x5, x2, (x3 + x4 + 2); Resolve_topsy.
      rewrite /Free_block_compact_size /= in H7 *; ssromega.
      right; left; by Resolve_topsy.
  + case => H5 [H9 [x4 [H8 [H11 [x5 [H10 H12]]]]]].
    subst x1.
    case: (In_hl_next _ _ _ _ _ _ _ H8 H10)=> x1 [x6 [H6 H13]] {H8 H10}.
    subst x2.
    rewrite /= (_ :
      x0 ++ (x3, topsy_hm.free) :: x1 ++ (x4, topsy_hm.free) :: (x5, topsy_hm.free) :: x6 =
      (x0 ++ (x3, topsy_hm.free) :: x1) ++ (x4, topsy_hm.free) :: (x5, topsy_hm.free) :: nil ++ x6) in H1; last first.
    by rewrite /= -!catA.
    case/Heap_List_compaction : H1 => x2 H6.
    case_sepcon H6.
    exists x2.
    Compose_sepcon h1 h2.
    rewrite 2!get_endl_app /= in H13 H6_h1.
    by Mapsto.
    move: H6_h2; apply monotony_imp => h'' H6.
    rewrite !get_endl_app /= in H13 *; by Mapsto.
    Resolve_topsy.
    exists x; Resolve_topsy.
    exists x0, nil, (x1 ++ (x4 + x5 + 2, topsy_hm.free) :: x6), x3; Resolve_topsy.
    set t := x0 ++ _.
    rewrite (_ : _ ++ _ = t) // in H6; by rewrite -!catA.
    right; right; Resolve_topsy.
    exists (x4 + x5 + 2); Resolve_topsy.
    apply In_hl_or_app; right => /=.
    rewrite /= !get_endl_app /= in H13 *.
    by rewrite -H13 !eqxx.

(** nptr <- var_e stts; *)

Step (fun s h => [ var_e hmStart ]e_ s = [ nat_e adr ]e_ s /\
    [ var_e result ]e_ s = [ null ]e_ s /\
    exists cur_adr, [ var_e cptr ]e_ s = [ nat_e cur_adr ]e_ s /\
      (exists l1 l l2 free_size,
        Heap_List (l1 ++ (free_size, topsy_hm.free) :: (Free_block_list l) ++ l2) adr s h /\
        Free_block_compact_size (free_size :: l) >= size /\
        ((cur_adr > 0 /\
            exists cur_size,
              In_hl l1 (cur_adr, cur_size, topsy_hm.free) adr /\
              [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s) \/
          (cur_adr > 0 /\ cur_adr = get_endl l1 adr /\
            [ var_e nptr \= nat_e (cur_adr + 2 + free_size) ]b_s) \/
          (l = nil /\ cur_adr > 0 /\
            exists cur_size,
              In_hl l2 (cur_adr, cur_size, topsy_hm.free) (get_endl (l1 ++ (free_size, topsy_hm.free) :: nil) adr) /\
              [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s)))).

rewrite /wp_assign.
case : H1 => [H2 [H4 [x [H3 [x0 [x1 [x2 [x3 [H1 [H7 H8]]]]]]]]]].
Resolve_topsy; rewrite eval_upd_subst //.
exists x; Resolve_topsy.
exists x0, x1, x2, x3; Resolve_topsy.
case : H8.
- case => H6 [x4 [H8 H9]].
  left; Resolve_topsy.
  exists x4; by Resolve_topsy.
- case.
  + case => H5 [H9 H10]; right; left; by Resolve_topsy.
  + case => H5 [H9 [x4 [H8 H10]]]; right; right; Resolve_topsy.
    exists x4; by Resolve_topsy.

(** stts <-* nptr -.> status *)

(** L *)

Step TT.
rewrite /while.entails => s h [H2 [H4 [x [H3 [x0 [x1 [x2 [x3 [H1 [H7 H8]]]]]]]]]].
rewrite /status.
case : H8.
- case => H6 [x4 [H8 H9]].
  move/In_hl_destruct : (H8) => [x5 [x6 [H11 H8']]].
  case: x6 H11 => [|[n b] x6] H11.
  + exists (hlstat_bool2expr topsy_hm.free).
    apply mapsto_strictly_exact; split.
    * Hl_getstatus H1 x3 H5; last by done.
      rewrite H11 get_endl_app /= in H5_h1; by Mapsto.
    * rewrite /wp_assign.
      Resolve_topsy; (rewrite eval_upd_subst //).
      exists x; Resolve_topsy.
      exists x5, (x3 :: x1), x2, x4; Resolve_topsy.
      set t := _ ++ _.
      rewrite (_ : x0 ++ _ = t) in H1; last by rewrite H11 /t; List_eq.
      by Resolve_topsy.
      rewrite /Free_block_compact_size /= in H7 *; ssromega.
      right; left; Resolve_topsy.
      right; left; Resolve_topsy.
      by move=> ?.
      exists x3, x1; Resolve_topsy.
  + exists (hlstat_bool2expr b).
    apply mapsto_strictly_exact; split.
    * rewrite H11 in H1; Hl_getstatus H1 n H5; last by done.
      rewrite get_endl_app /= H8' in H5_h1; by Mapsto.
    * rewrite /wp_assign.
      Resolve_topsy; (rewrite eval_upd_subst //).
      exists x; Resolve_topsy.
      exists x0, x1, x2, x3; Resolve_topsy.
      left; Resolve_topsy.
      exists x4; Resolve_topsy.
      left; exists b, n; Resolve_topsy.
      rewrite H11; apply In_hl_or_app; right => /=.
      case: ifP => // _.
      by rewrite H8' !eqxx.
    by destruct b; rewrite eval_b_upd_subst.
- case.
  + case => H5 [H9 H10].
    case: x1 H1 H7 => [|n x1] H1 H7; simpl in H1.
    * case: x2 H1 => [|[n b] x2] H1.
      * exists (hlstat_bool2expr alloc).
        apply mapsto_strictly_exact; split.
        move/hl_getstat_last : H1 => H1; case_sepcon H1.
        Compose_sepcon h1 h2; last by done.
        rewrite get_endl_app /= -H9 in H1_h1; by Mapsto.
        rewrite /wp_assign.
        Resolve_topsy; (rewrite eval_upd_subst //).
        exists x; Resolve_topsy.
        exists x0, nil, nil, x3; Resolve_topsy.
        right; left; Resolve_topsy.
        right; right; Resolve_topsy.
        rewrite get_endl_app /=; ssromega.
      * exists (hlstat_bool2expr b).
        apply mapsto_strictly_exact; split.
        Hl_getstatus H1 n H6; last by done.
        rewrite get_endl_app /= -H9 in H6_h1; by Mapsto.
        rewrite /wp_assign.
        Resolve_topsy; (rewrite eval_upd_subst //).
        exists x; Resolve_topsy.
        exists x0, nil, ((n, b) :: x2), x3; Resolve_topsy.
        right; left; Resolve_topsy.
        left; Resolve_topsy.
        exists b, n; Resolve_topsy.
        by rewrite /= get_endl_app /= H9 !eqxx.
        by destruct b; rewrite eval_b_upd_subst.
    * exists (hlstat_bool2expr topsy_hm.free).
      apply mapsto_strictly_exact; split.
      Hl_getstatus H1 n H6; last by done.
      rewrite get_endl_app /= -H9 in H6_h1; by Mapsto.
      rewrite /wp_assign.
      Resolve_topsy; (rewrite eval_upd_subst //).
      exists x; Resolve_topsy.
      exists x0, (n :: x1), x2, x3; Resolve_topsy.
      right; left; Resolve_topsy.
      right; left; Resolve_topsy.
      done.
      exists n, x1; by Resolve_topsy.
  + case => H5 [H9 [x4 [H8 H10]]].
    subst x1; simpl in H1.
    move/In_hl_destruct : (H8) => [x5 [x6 [H11 H12]]].
    case: x6 H11 => [|[n b] x6] H11.
    * exists (hlstat_bool2expr alloc).
      apply mapsto_strictly_exact; split.
      move/hl_getstat_last : H1 => H1; case_sepcon H1.
      Compose_sepcon h1 h2; last by done.
      rewrite /= get_endl_app /= in H12.
      rewrite get_endl_app /= H11 /= get_endl_app /= in H1_h1; by Mapsto.
      rewrite /wp_assign.
      Resolve_topsy; (rewrite eval_upd_subst //).
      exists x; Resolve_topsy.
      exists x0, nil, x2, x3; Resolve_topsy.
      right; right; Resolve_topsy.
      exists x4; Resolve_topsy.
      right; split.
      by rewrite get_endl_app /= H11 -H12 !get_endl_app.
      by rewrite eval_b_upd_subst.
    * exists (hlstat_bool2expr b).
      apply mapsto_strictly_exact; split.
      rewrite H11 in H1; Hl_getstatus H1 n H5; last by done.
      rewrite get_endl_app /= in H12.
      rewrite get_endl_app /= get_endl_app /= H12 in H5_h1; by Mapsto.
      rewrite /wp_assign.
      Resolve_topsy; (rewrite eval_upd_subst //).
      exists x; Resolve_topsy.
      exists x0, nil, x2, x3; Resolve_topsy.
      right; right; Resolve_topsy.
      exists x4; Resolve_topsy.
      left; exists b, n; split.
      rewrite H11; apply In_hl_or_app; right => /=.
      case: ifP => // _.
      by rewrite H12 !eqxx.
    by destruct b; rewrite eval_b_upd_subst.

(** skip *)

Step TT.
rewrite /while.entails => s h [[H2 [H4 [x [H3' [x0 [x1 [x2 [x3 [H1 [H7 H9]]]]]]]]]] H3].
Resolve_topsy.
exists x; Resolve_topsy.
exists x0, x1, x2, x3; Resolve_topsy.
case : H9.
- case=> n_gt_0 [x4 [x5 [H6 H9]]].
  left; Resolve_topsy.
  by exists x4, x5.
- case.
  + case => H6 [H10] ?.
    exfalso. omegab.
  + case.
    * case => x_gt_0 [H10 [x4 [x5 [H6 H9]]]].
      right; right; left; Resolve_topsy.
      by exists x4, x5.
    * case => x_gt_0 [H10 [H9 H6]].
      right; right; right; by Resolve_topsy.

(** cptr <-* cptr -.> next *)

Step TT.
rewrite /while.entails => s h [H2 [H4 [x [H3 [x0 [x1 [x2 [x3 [H1 [H7 H8]]]]]]]]]].
rewrite /next.
case: H8.
- case => H6 [x4 [x5 H8]].
  exists (nat_e (x + 2 + x4)).
  move/In_hl_destruct : H8 => [x6 [x7 [H10 H11]]].
  apply mapsto_strictly_exact; split.
  rewrite H10 in H1; Hl_getnext H1 x4 H5; [by Mapsto | done].
  rewrite /wp_assign.
  Resolve_topsy; (rewrite eval_upd_subst //).
  exists (x + 2 + x4); Resolve_topsy.
  exists x0, x1, x2, x3; Resolve_topsy.
  case : x7 H10 => [| [n b] x7 ] H10.
  + right; left; Resolve_topsy.
    ssromega.
    by rewrite H10 get_endl_app /= H11.
  + left.
    split; first by ssromega.
    exists n, b.
    rewrite H10; apply In_hl_or_app; right => /=.
    set t' := _ && _.
    destruct t' => //=.
    by rewrite H11 !eqxx.
- case.
  + case=> H5 [H9 H10].
    subst x1; simpl in H1.
    exists (nat_e (x + 2 + x3)).
    apply mapsto_strictly_exact; split.
    Hl_getnext H1 x3 H6; [by Mapsto | done].
    rewrite /wp_assign; Resolve_topsy; (rewrite eval_upd_subst //).
    exists (x + 2 + x3); Resolve_topsy.
    exists x0, nil, x2, x3; Resolve_topsy.
    case : x2 H1 => [| [n b] x2 ] H1.
    * right; right; right; left; Resolve_topsy.
      ssromega.
      rewrite get_endl_app /=; ssromega.
    * right; right; left; Resolve_topsy.
      ssromega.
      exists n, b; by rewrite /= get_endl_app /= H9 !eqxx.
  + case.
    * case => H6 [H9 [x4 [x5 H8]]].
      subst x1.
      exists (nat_e (x + 2 + x4)).
      move/In_hl_destruct : H8 => [x6 [x7 [H10 H11]]].
      apply mapsto_strictly_exact; split.
      rewrite H10 in H1; Hl_getnext H1 x4 H5; last by done.
      rewrite !get_endl_app /= in H11 H5_h1; by Mapsto.
      rewrite /wp_assign.
      Resolve_topsy; (rewrite eval_upd_subst //).
      exists (x + 2 + x4); Resolve_topsy.
      exists x0, nil, x2, x3; Resolve_topsy.
      case : x7 H10 => [|[n b] x7] H10.
      - right; right; right; left; Resolve_topsy.
        ssromega.
        rewrite /= !get_endl_app /= in H11 *.
        by rewrite H10 get_endl_app /= H11.
      - right; right; left; Resolve_topsy.
        ssromega.
        exists n, b.
        rewrite H10; apply In_hl_or_app; right; simpl.
        case: ifP => //=.
        by rewrite H11 !eqxx.
    * case => H6 [H9 H10].
      subst x1.
      exists (nat_e 0).
      apply mapsto_strictly_exact; split.
      move/hl_getnext_last : H1 => H1; case_sepcon H1.
      Compose_sepcon h1 h2; [by Mapsto | done].
      rewrite /wp_assign; Resolve_topsy; (rewrite eval_upd_subst //).
      exists 0; Resolve_topsy.
      exists x0, nil, x2, x3; Resolve_topsy.
      tauto.
Qed.

(** the second call to findFree will always find a free enough block *)

Definition findFree_specif2' := forall adr size, size > 0 -> adr > 0 ->
  {{ fun s h => exists l, Heap_List l adr s h /\
    [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
    [ var_e result ]e_s = [ null ]e_s /\
    exists free_adr free_size,
      free_size >= size /\ In_hl l (free_adr, free_size, topsy_hm.free) adr }}
  findFree size entry fnd sz stts
  {{ fun s h => exists l, Heap_List l adr s h /\
    [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
    [ var_e result ]e_s = [ null ]e_s /\
    exists found_free_block size'', size'' >= size /\
      In_hl l (found_free_block, size'', topsy_hm.free) adr /\
      [ var_e entry ]e_s = Z_of_nat found_free_block /\
      found_free_block > 0 }}.

Lemma findFree_verif2' : findFree_specif2'.
Proof.
rewrite /findFree_specif2' => adr size H H0.
rewrite /findFree.

Step (fun s h => exists l1 l2 free_size,
  free_size >= size /\
  Heap_List (l1 ++ (free_size, topsy_hm.free) :: l2) adr s h /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  [ var_e entry ]e_ s = [ nat_e adr ]e_s).

case : H1 => x [H1 [H4 [H3 [x0 [x1 [H2 H6]]]]]].
rewrite /wp_assign.
move/In_hl_destruct : (H6) => [x2 [x3 [H7 H8]]].
exists x2, x3, x1.
rewrite -H7.
by Resolve_topsy; rewrite eval_upd_subst.

Step (fun s h => exists l1 l2 free_size,
  free_size >= size /\
  Heap_List (l1 ++ (free_size, topsy_hm.free) :: l2) adr s h /\
  [ var_e hmStart ]e_ s = [ nat_e adr ]e_s /\
  [ var_e result ]e_s = [ null ]e_s /\
  [ var_e entry ]e_s = [ nat_e adr ]e_ s).

case : H1 => x [x0 [x1 [H1 [H4 [H3 [H5 H7]]]]]].
unfold status.
case: x H4 => [|[n b] x] H4.
- simpl in H4.
  exists (hlstat_bool2expr topsy_hm.free).
  apply mapsto_strictly_exact; split.
  Hl_getstatus H4 x1 H2; [by Mapsto | done].
  rewrite /wp_assign.
  exists nil, x0, x1.
  by Resolve_topsy; rewrite eval_upd_subst.
- exists (hlstat_bool2expr b).
  apply mapsto_strictly_exact; split.
  Hl_getstatus H4 n H2; [by Mapsto | done].
  rewrite /wp_assign.
  exists ((n, b) :: x), x0, x1.
  by Resolve_topsy; rewrite eval_upd_subst.

Step (fun s h => exists l1 l2 free_size,
  free_size >= size /\
  Heap_List (l1 ++ (free_size, topsy_hm.free)::l2) adr s h /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_ s /\
  [ var_e result ]e_s = [ null ]e_s /\
  [ var_e entry ]e_s = [ nat_e adr ]e_s /\
  [ var_e fnd ]e_s = [ nat_e 0 ]e_s).

rewrite /wp_assign.
case : H1 => x [x0 [x1 [H1 [H4 [H3 [H5 H7]]]]]].
exists x, x0, x1.
by Resolve_topsy; rewrite eval_upd_subst.

Step (fun s h => exists l1 l2 free_size,
  free_size >= size /\
  Heap_List (l1 ++ (free_size, topsy_hm.free) :: l2) adr s h /\
  [ var_e hmStart ]e_ s = [ nat_e adr ]e_s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  exists cur_adr,
    [ var_e entry ]e_s = [ nat_e cur_adr ]e_s /\
    ((exists cur_size cur_status,
      In_hl l1 (cur_adr,cur_size,cur_status) adr /\
      ([ var_e fnd ]e_ s = [ nat_e 0 ]e_ s \/
        ([ var_e fnd ]e_ s = [ nat_e 1 ]e_s /\
          cur_size >= size /\
          cur_status = topsy_hm.free))) \/
    cur_adr = get_endl l1 adr)).

rewrite /while.entails => s h [x [x0 [x1 [H1 [H4 [H3 [H5 [H6 H8]]]]]]]].
exists x, x0, x1; Resolve_topsy.
exists adr; Resolve_topsy.
case: x H4 => [|[n b] x] H4.
by right.
left; exists n, b; Resolve_topsy.
by rewrite /= !eqxx.

rewrite /while.entails => s h [[x [x0 [x1 [H1 [H4 [H7 [H5 [x2 [H9 H8]]]]]]]]] H3].
case : H8 => H8.
- case : H8 => x3 [x4 [H8 H2]].
  case : H2 => [H2|].
  + move/In_hl_ge_start : H8 => H8.
    suff : False by contradiction.
    rewrite /hoare_m.eval_b in H3; by omegab.
  + case => H2 [H11 H12].
    exists (x ++ (x1, topsy_hm.free) :: x0); Resolve_topsy.
    exists x2, x3; Resolve_topsy.
    subst x4.
    apply In_hl_or_app; by left.
    move: (In_hl_ge_start _ _ _ _ _ H8) => ?; ssromega.
- exists (x ++ (x1, topsy_hm.free) :: x0); Resolve_topsy.
  exists (get_endl x adr), x1; Resolve_topsy.
  apply In_hl_or_app; right.
  by rewrite /= !eqxx.
  by rewrite H9 H8.
  move: (get_endl_gt x adr) => ?; ssromega.

Step (fun s h => exists l1 l2 free_size,
  free_size >= size /\
  Heap_List (l1 ++ (free_size, topsy_hm.free) :: l2) adr s h /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_s = [ null ]e_s /\
  exists cur_adr,
    [ var_e entry ]e_ s = [ nat_e cur_adr ]e_ s /\
    ((exists cur_size cur_status,
          In_hl l1 (cur_adr,cur_size,cur_status) adr /\
          [ var_e fnd ]e_ s = [ nat_e 0 ]e_ s /\
          [ var_e stts ]e_ s = [ hlstat_bool2expr cur_status ]e_ s) \/
      (cur_adr = get_endl l1 adr /\
        [ var_e stts ]e_s = [ hlstat_bool2expr topsy_hm.free ]e_s))).

case : H1 => [[x [x0 [x1 [H1 [H4 [H7 [H5 [x2 [H9 H8]]]]]]]]] H3'].
case : H8 => H3.
- case : H3 => x3 [x4 [H8 H10]].
  case: H10 => H3.
  + unfold status.
    exists (hlstat_bool2expr x4).
    apply mapsto_strictly_exact; split.
    move/In_hl_destruct : H8 => [x5 [x6 [H12 H13]]].
    rewrite H12 in H4; Hl_getstatus H4 x3 H8; [by Mapsto | done].
    rewrite /wp_assign.
    exists x, x0, x1; Resolve_topsy; rewrite eval_upd_subst => //.
    exists x2; Resolve_topsy; try (rewrite eval_upd_subst //).
    left; exists x3, x4; Resolve_topsy; try (rewrite eval_upd_subst //).
    by destruct x4; rewrite eval_upd_subst.
  + case : H3 => H10 [H12 H13].
    suff : False by done. omegab.
- rewrite /status.
  exists (hlstat_bool2expr topsy_hm.free).
  apply mapsto_strictly_exact; split.
  Hl_getstatus H4 x1 H8; [by Mapsto | done].
  rewrite /wp_assign.
  exists x, x0, x1; Resolve_topsy; try (rewrite eval_upd_subst //).
  exists x2; Resolve_topsy; try (rewrite eval_upd_subst //).
  right; by Resolve_topsy; rewrite eval_upd_subst.

Step (fun s h => exists l1 l2 free_size,
  free_size >= size /\
  Heap_List (l1 ++ (free_size, topsy_hm.free)::l2) adr s h /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_ s = [ null ]e_s /\
  (exists cur_adr,
    [ var_e entry ]e_s = [ nat_e cur_adr ]e_s /\
    ((exists cur_size cur_status,
      In_hl l1 (cur_adr, cur_size, cur_status) adr /\
      [ var_e fnd ]e_s = [ nat_e 0 ]e_s /\
      [ var_e stts ]e_s = [ hlstat_bool2expr cur_status ]e_s /\
      [ var_e sz ]e_ s = [ nat_e cur_size ]e_ s) \/
    (cur_adr = get_endl l1 adr  /\
      [ var_e stts ]e_ s = [ hlstat_bool2expr topsy_hm.free ]e_s /\
      [ var_e sz ]e_s = [ nat_e free_size ]e_s)))).

rewrite /ENTRYSIZE.

Step (fun s h => exists l1 l2 free_size,
  free_size >= size /\
  Heap_List (l1 ++ (free_size, topsy_hm.free) :: l2) adr s h /\
  [ var_e hmStart ]e_ s = [ nat_e adr ]e_s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  exists cur_adr,
    [ var_e entry ]e_ s = [ nat_e cur_adr ]e_s /\
    ((exists cur_size cur_status,
          In_hl l1 (cur_adr, cur_size, cur_status) adr /\
          [ var_e fnd ]e_s = [ nat_e 0 ]e_ s /\
          [ var_e stts ]e_ s = [ hlstat_bool2expr cur_status ]e_s /\
          [ var_e sz ]e_ s = [ nat_e (cur_adr + 2 + cur_size) ]e_s) \/
      (cur_adr = get_endl l1 adr /\
        [ var_e stts ]e_s = [ hlstat_bool2expr topsy_hm.free ]e_s /\
        [ var_e sz ]e_s = [ nat_e (cur_adr + 2 + free_size) ]e_s))).

case : H1 => [x [x0 [x1 [H1 [H4 [H3 [H5 [x2 [H6 H7]]]]]]]]].
unfold next.
case : H7.
- case => x3 [x4 [H7 [H9 H10]]].
  exists (nat_e (x2 + 2 + x3)).
  apply mapsto_strictly_exact; split.
  move/In_hl_destruct : H7 => [x5 [x6 [H11 H12]]].
  rewrite H11 in H4; Hl_getnext H4 x3 H2; [by Mapsto | done].
  rewrite /wp_assign.
  exists x, x0, x1; Resolve_topsy; try (rewrite eval_upd_subst //).
  exists x2; Resolve_topsy; try (rewrite eval_upd_subst //).
  left; exists x3, x4; Resolve_topsy; try (rewrite eval_upd_subst //).
  by destruct x4; rewrite eval_upd_subst.
- case => H7 H8.
  exists (nat_e (x2 + 2 + x1)).
  apply mapsto_strictly_exact; split.
  Hl_getnext H4 x1 H2; [Mapsto | done].
  rewrite /wp_assign.
  exists x, x0, x1; Resolve_topsy; try (rewrite eval_upd_subst //).
  exists x2; Resolve_topsy; try (rewrite eval_upd_subst //).
  right; by Resolve_topsy; rewrite eval_upd_subst.

Step (fun s h => exists l1 l2 free_size, free_size >= size /\
  Heap_List (l1 ++ (free_size, topsy_hm.free) :: l2) adr s h /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_s = [ null ]e_s /\
  exists cur_adr, [ var_e entry ]e_s = [ nat_e cur_adr ]e_s /\
    ((exists cur_size cur_status,
      In_hl l1 (cur_adr,cur_size,cur_status) adr /\
      [ var_e fnd ]e_s = [ nat_e 0 ]e_s /\
      [ var_e stts ]e_s = [ hlstat_bool2expr cur_status ]e_s /\
      [ var_e sz ]e_s =  [ nat_e cur_size ]e_s) \/
    (cur_adr = get_endl l1 adr /\
      [ var_e stts ]e_s = [ hlstat_bool2expr topsy_hm.free ]e_s /\
      [ var_e sz ]e_s = [ nat_e free_size ]e_s))).

case : H1 => x [x0 [x1 [H1 [H4 [H3 [H5 [x2 [H6 H7]]]]]]]].
case : H7.
- case => x3 [x4 [H7 [H9 [H8 H11]]]].
  rewrite /wp_assign.
  exists x, x0, x1; Resolve_topsy.
  by rewrite eval_upd_subst.
  by rewrite eval_upd_subst.
  exists x2; Resolve_topsy.
  by rewrite eval_upd_subst.
  left; exists x3, x4; Resolve_topsy.
  by rewrite eval_upd_subst.
  destruct x4; by rewrite eval_upd_subst.
  rewrite !eval_upd_subst /=; omegab.
- case => H7 [H9 H10].
  rewrite /wp_assign.
  exists x, x0, x1; Resolve_topsy.
  by rewrite eval_upd_subst.
  by rewrite eval_upd_subst.
  exists x2; Resolve_topsy.
  by rewrite eval_upd_subst.
  right; Resolve_topsy.
  by rewrite eval_upd_subst.
  rewrite !eval_upd_subst /=; by omegab.

Step TT.

Step TT.

move=> s h [[x [x0 [x1 [H1 [H4 [H3 [H5 [x2 [H6 H8]]]]]]]]] H7].
case: H8 => H8.
case : H8 => x3 [x4 [H1' [H10 [H9 H12]]]].
exfalso. by omegab.
exfalso. by omegab.

Step TT.

rewrite /while.entails; intros; tauto.

Step TT.

Step TT.

move=> s h [[x [x0 [x1 [H1 [H4 [H3 [H5 [x2 [H6 H8]]]]]]]]] H7].
case : H8.
- case => x3 [x4 [H8 [H11 [H10 H13]]]].
  rewrite /wp_assign.
  exists x, x0, x1; Resolve_topsy; try (rewrite eval_upd_subst //).
  exists x2; Resolve_topsy; try (rewrite eval_upd_subst //).
  left; exists x3, x4; Resolve_topsy; try (rewrite eval_upd_subst //).
  right; Resolve_topsy; try (rewrite eval_upd_subst //).
  omegab.
  rewrite /= in H10 H7.
  rewrite H10 in H7.
  by destruct x4.
- case => H8 [H11 H12].
  rewrite /wp_assign.
  exists x, x0, x1; Resolve_topsy; try (rewrite eval_upd_subst //).
  exists x2; by Resolve_topsy; rewrite eval_upd_subst.

Step TT.
rewrite /while.entails => s h [[x [x0 [x1 [H1 [H4 [H3 [H5 [x2 [H6 H8]]]]]]]]] H7].
rewrite /next.
case : H8 => H8.
- case : H8 => x3 [x4 [H8 [H10 [H9 H12]]]].
  exists (nat_e (x2 + 2 + x3)).
  move/In_hl_destruct : H8 => [x5 [x6 [Hx H14]]].
  apply mapsto_strictly_exact; split.
  rewrite Hx in H4; Hl_getnext H4 x3 H2; [by Mapsto | done].
  rewrite /wp_assign.
  exists x, x0, x1; Resolve_topsy; try (rewrite eval_upd_subst //).
  exists (x2 + 2 + x3); Resolve_topsy; try (rewrite eval_upd_subst //).
  case : x6 Hx => [|[n b] x6] Hx.
  + right; by rewrite Hx get_endl_app /=; auto.
  + left; exists n, b.
    Resolve_topsy; try (rewrite eval_upd_subst //).
    rewrite Hx; apply In_hl_or_app; right => /=.
    case: ifP => // _.
    by rewrite H14 !eqxx.
- exfalso. by omegab.
Qed.

(* The splitting will be performed as usual (previous proof is reusable??) *)

Definition split_specif2 := forall adr size, size > 0 -> adr > 0 ->
  {{ fun s h =>  exists l, Heap_List l adr s h /\
    [ var_e hmStart ]e_s = [ nat_e adr ]e_ s /\
    [ var_e result ]e_s = [ null ]e_s /\
    exists found_free_block size'', size'' >= size /\
      In_hl l (found_free_block, size'', topsy_hm.free) adr /\
      [ var_e entry ]e_s = Z_of_nat found_free_block /\
      found_free_block > 0 }}
  split entry size cptr sz
    {{ fun s h => exists l y, y > 0 /\ [ var_e entry ]e_s = Z_of_nat y /\
        exists size'', size'' >= size /\
          (Heap_List l adr ** Array (y + 2) size'') s h /\
          In_hl l (y, size'', alloc) adr }}.

Lemma split_verif2 : split_specif2.
Proof.
rewrite /split_specif2 => adr size H H0; rewrite /split.

Step (fun s h => exists l, Heap_List l adr s h /\
  [ var_e hmStart ]e_ s = [ nat_e adr ]e_s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  exists found_free_block size'', size'' >= size /\
    In_hl l (found_free_block,size'', topsy_hm.free) adr /\
    [ var_e entry ]e_ s = Z_of_nat found_free_block /\
    found_free_block > 0 /\
    [ var_e sz ]e_s = [ nat_e size'' ]e_s).

rewrite /ENTRYSIZE.

Step (fun s h => exists l, Heap_List l adr s h /\
  [ var_e hmStart ]e_ s = [ nat_e adr ]e_ s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  exists found_free_block size'', size'' >= size /\
    In_hl l (found_free_block,size'', topsy_hm.free) adr /\
    [ var_e entry ]e_s = Z_of_nat found_free_block /\
    found_free_block > 0 /\
    [ var_e sz ]e_ s = [ nat_e (found_free_block + 2 + size'') ]e_s).

case : H1 => x [H1 [H3 [H4 [x0 [x1 [H2 [H7 [H6 H9]]]]]]]].
exists (nat_e (x0 + 2 + x1)).
unfold next.
apply mapsto_strictly_exact; split.
move/In_hl_destruct : H7 => [x2 [x3 [H10 H11]]].
rewrite H10 in H1; Hl_getnext H1 x1 H5; [by Mapsto | done].
rewrite /wp_assign.
exists x; Resolve_topsy; try (rewrite eval_upd_subst //).
exists x0, x1; by Resolve_topsy; rewrite eval_upd_subst.

Step (fun s h => exists l, Heap_List l adr s h /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_s = [ null ]e_s /\
  exists found_free_block size'', size'' >= size /\
    In_hl l (found_free_block, size'', topsy_hm.free) adr /\
    [ var_e entry ]e_s = Z_of_nat found_free_block /\
    found_free_block > 0 /\
    [ var_e sz ]e_s = [ nat_e size'' ]e_s).

case : H1 => x [H1 [H3 [H4 [x0 [x1 [H2 [H7 [H6 [H8 H9]]]]]]]]].
rewrite /wp_assign.
exists x; Resolve_topsy; try (rewrite eval_upd_subst //).
exists x0, x1; Resolve_topsy; try (rewrite eval_upd_subst //).
rewrite !eval_upd_subst /=.
omegab.

Step TT.

Step TT.

move=> s h H1.
case : H1 => [[x [H1 [H3 [H4 [x0 [x1 [H2 [H7 [H6 [H8 H9]]]]]]]]]] H3'].
suff : False by done. by omegab.

Step TT.

rewrite /while.entails => s h [[x [H1 [H3 [H4 [x0 [x1 [H2 [H7 [H6 [H8 H9]]]]]]]]]] H3'].
exists x; Resolve_topsy.
exists x0, x1; by Resolve_topsy.

Step (fun s h => exists l, Heap_List l adr s h /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_s = [ null ]e_s /\
  exists found_free_block size'', size'' >= size /\
    In_hl l (found_free_block, size'', topsy_hm.free) adr /\
    [ var_e entry ]e_s = Z_of_nat found_free_block /\
    found_free_block > 0).

Step (fun s h => exists l, Heap_List l adr s h /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_s = [ null ]e_s /\
  exists found_free_block size'',
    size'' >= size + LEFTOVER + 2 /\
    In_hl l (found_free_block, size'', topsy_hm.free) adr /\
    [ var_e entry ]e_s = Z_of_nat found_free_block /\
    found_free_block > 0 /\
    [ var_e sz ]e_s = [ nat_e size'' ]e_s /\
    [ var_e cptr ]e_s = [ nat_e (found_free_block + 2 + size) ]e_s).

case : H1 => [[x [H1 [H3 [H4 [x0 [x1 [H2 [H7 [H6 [H8 H9]]]]]]]]]] H3'].
rewrite /wp_assign.
exists x; Resolve_topsy; try (rewrite eval_upd_subst //).
exists x0, x1; Resolve_topsy; try (rewrite eval_upd_subst //).
rewrite /LEFTOVER; by omegab.
rewrite /= in H6.
rewrite !eval_upd_subst /= H6; by omegab.

Step (fun s h => exists l, Heap_List l adr s h /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_s /\
  [ var_e result ]e_s = [ null ]e_s /\
  exists found_free_block size'',
    size'' >= size + LEFTOVER + 2 /\
    In_hl l (found_free_block,size'', topsy_hm.free) adr /\
    [ var_e entry ]e_s = Z_of_nat found_free_block /\
    found_free_block > 0 /\
    [ var_e sz ]e_s = [ nat_e (found_free_block + 2 + size'') ]e_s /\
    [ var_e cptr ]e_s = [ nat_e (found_free_block + 2 + size) ]e_s).

case: H1 => l [Hl [HhmStart [Hresult
  [found_free_block [size'' [Hsize'' [Hl' [Hentry [Hfound_free_block [Hsz Hcptr]]]]]]]]]].
exists (nat_e (found_free_block + 2 + size'')).
apply mapsto_strictly_exact; split.
move/In_hl_destruct : Hl' => [x [x0 [H3 H4]]].
rewrite H3 in Hl; Hl_getnext Hl size'' H1; last by done.
rewrite /next; by Mapsto.

rewrite /wp_assign; exists l.
Resolve_topsy; try (rewrite eval_upd_subst //).
exists found_free_block, size''; by Resolve_topsy; rewrite eval_upd_subst.

Step (fun s h => exists e'',
    ((cptr -.> status) |~> e'' **
      ((cptr -.> status) |~> Free -*
       (fun s0 h0 => exists e''0,
          ((entry -.> next) |~> e''0 **
           (entry -.> next |~> var_e cptr -*
             (fun s1 h1 => exists l,
               Heap_List l adr s1 h1 /\
               [ var_e hmStart ]e_s1 = [ nat_e adr ]e_s1 /\
               [ var_e result ]e_s1 = [ null ]e_s1 /\
               exists found_free_block size'',
                 size'' >= size /\
                 In_hl l (found_free_block, size'', topsy_hm.free) adr /\
                 [ var_e entry ]e_s1 = Z_of_nat found_free_block /\
                 found_free_block > 0))) s0 h0))) s h).

case : H1 => x [H1 [H4 [H5 [x0 [x1 [H2 [H7 [H6 [H8 [H9 H10]]]]]]]]]].
rewrite (_ : x1 = size + 2 + (x1 - 2 - size)) in H7; last by ssromega.
move/In_hl_destruct : H7 => [x2 [x3 [H12 H13]]].
rewrite H12 in H1; case/Heap_List_splitting : H1 => x' H1.
exists x'.
rewrite /next /status.
case_sepcon H1.
Compose_sepcon h1 h2; first by Mapsto.
move: H1_h2; apply monotony_imp => h'' Hh''; first by Mapsto.
case: Hh'' => x4 H18.
exists x4.
case_sepcon H18.
Compose_sepcon h''1 h''2; first by Mapsto.
move: H18_h''2; apply monotony_imp => h''0 Hh''0; first by Mapsto.
case: Hh''0 => x5 H14.
exists x5.
case_sepcon H14.
Compose_sepcon h''01 h''02; first by Mapsto.
move: H14_h''02; apply monotony_imp => h''3 Hh''3; first by Mapsto.
exists (x2 ++ (size, true) :: (x1 - 2 - size, true) :: x3); Resolve_topsy.
exists x0, size; Resolve_topsy.
apply In_hl_or_app; right => /=.
by rewrite H13 !eqxx.

Step (fun s0 h0 => exists e'',
  (entry -.> next |~> e'' **
    (entry -.> next |~> var_e cptr -*
      (fun s h => exists l,
        Heap_List l adr s h /\
        [ var_e hmStart ]e_ s = [ nat_e adr ]e_s /\
        [ var_e result ]e_s = [ null ]e_s /\
        exists found_free_block size'',
          size'' >= size /\
          In_hl l (found_free_block, size'', topsy_hm.free) adr /\
          [ var_e entry ]e_s = Z_of_nat found_free_block /\
          found_free_block > 0))) s0 h0).

exact H1.

Step TT.
by apply hoare_prop_m.entails_id.

Step TT.
rewrite /while.entails => s h [[x [H1 [H3 [H4 [x0 [x1 [H2 [H7 [H6 [H8 H9]]]]]]]]]] H3'].
exists x; Resolve_topsy.
exists x0, x1; by Resolve_topsy.

Step TT.
rewrite /while.entails => s h [x [H1 [H3 [H4 [x0 [x1 [H2 [H7 [H6 H8]]]]]]]]].
rewrite /status.
move/In_hl_destruct : H7 => [x2 [x3 [H10 H11]]].
rewrite H10 in H1; case/hl_free2alloc : H1 => x' H1.
exists x'.
case_sepcon H1.
Compose_sepcon h1 h2; first by Mapsto.
move: H1_h2; apply monotony_imp => h' Hh'; first by Mapsto.
exists (x2 ++ (x1, false) :: x3), x0; Resolve_topsy.
exists x1; Resolve_topsy.
case_sepcon Hh'.
Compose_sepcon h'1 h'2.
by Resolve_topsy.
by rewrite -H11.
apply In_hl_or_app; right => /=.
by rewrite H11 !eqxx.
Qed.

Definition hmAlloc_specif2 := forall adr size, adr > 0 -> size > 0 ->
  {{ fun s h => exists l1 l2 l,
     (Heap_List (l1 ++ Free_block_list l ++ l2) adr) s h /\
     Free_block_compact_size l >= size /\
     [ var_e hmStart \= nat_e adr ]b_s }}
  hmAlloc result size entry cptr fnd stts nptr sz
  {{ fun s h => exists l y,
     y > 0 /\ [ var_e result \= nat_e (y + 2) ]b_s /\
     exists size'', size'' >= size /\
       (Heap_List l adr ** Array (y + 2) size'') s h /\
       In_hl l (y, size'', alloc) adr }}.

Lemma hmAlloc_verif2 : hmAlloc_specif2.
Proof.
rewrite /hmAlloc_specif2 /hmAlloc => adr size H H0.

Step (fun s h => exists l1 l2 l,
    (Heap_List (l1 ++ Free_block_list l ++ l2) adr) s h /\
    Free_block_compact_size l >= size /\
    [ var_e hmStart \= nat_e adr ]b_s /\
    [ var_e result \= null ]b_s).

rewrite /wp_assign.
case: H1 => x [x0 [x1 [H1 [H4 H5]]]].
exists x, x0, x1; by Resolve_topsy.

Step (fun s h => exists l1 l2 l,
  (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
  (Free_block_compact_size l) >= size /\
  [ var_e hmStart ]e_ s = [ nat_e adr ]e_s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  ((exists found_free_block size'', size'' >= size /\
      In_hl (l1 ++ (Free_block_list l) ++ l2) (found_free_block, size'', topsy_hm.free) adr /\
      [ var_e entry ]e_s = Z_of_nat found_free_block /\
      found_free_block > 0) \/
    [ var_e entry ]e_s = [ null ]e_ s)).

move: (findFree_verif2 adr size H0 H) => H1.

Step TT.
rewrite /while.entails => {H1} s h [x [x0 [x1 [H1 [H4 [H3 [H5 H7]]]]]]].
exists x, x0, x1; by Resolve_topsy.
rewrite /while.entails => {H1} s h [x [x0 [x1 [H1 [H4 [H3 H5]]]]]].
exists x, x0, x1; Resolve_topsy.
by omegab.
by omegab.

Step (fun s h => exists l, Heap_List l adr s h /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_ s /\
  [ var_e result ]e_s = [ null ]e_ s /\
  exists found_free_block size'',
    size'' >= size /\
    In_hl l (found_free_block, size'', topsy_hm.free) adr /\
    [ var_e entry ]e_s = Z_of_nat found_free_block /\
    found_free_block > 0).

Step (fun s h => exists l1 l2 l,
  (Heap_List (l1 ++ (Free_block_list l) ++ l2) adr) s h /\
  Free_block_compact_size l >= size /\
  [ var_e hmStart ]e_s = [ nat_e adr ]e_ s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  [ var_e entry ]e_ s = [ null ]e_ s /\
  [ var_e cptr ]e_ s = [ nat_e adr ]e_ s).

case : H1 => [[x [x0 [x1 [H1 [H4 [H3 [H5 H8]]]]]]] Heq].
case : H8 => H8.
- case: H8 => x2 [x3 [H7 [H9 [H8 H11]]]].
  suff : False by done. omegab.
- rewrite /wp_assign; exists x, x0, x1.
  by Resolve_topsy; rewrite eval_upd_subst.

Step (fun s h => exists l, (Heap_List l adr) s h /\
  [ var_e hmStart ]e_ s = [ nat_e adr ]e_ s /\
  [ var_e result ]e_ s = [ null ]e_ s /\
  exists free_adr free_size, free_size >= size /\
    In_hl l (free_adr, free_size, topsy_hm.free) adr).

move: (compact_verif2 adr size H0 H) => H1.

Step TT. (* apply hoare_conseq (?) *)
- by apply hoare_prop_m.entails_id.
- clear H1.
  rewrite /while.entails => s h [x [x0 [x1 [H1 [H4 [H3 [H5 [H6 H8]]]]]]]].
  exists x, x0, x1.
  Resolve_topsy; by rewrite eval_upd_subst.

move: (findFree_verif2' adr size H0 H) => H1.

Step TT.
by apply hoare_prop_m.entails_id.
by apply hoare_prop_m.entails_id.

Step TT.

rewrite /while.entails => s h [[x [x0 [x1 [H1 [H4 [H3 [H5 H8]]]]]]] Heq].
case : H8 => H8.
- case : H8 => x2 [x3 [H7 [H9 [H8 H11]]]].
  exists (x ++ Free_block_list x1 ++ x0); Resolve_topsy.
  exists x2, x3; by Resolve_topsy.
- suff : False by done. omegab.

Step TT.

Step TT.
move=> s h [[x [H2 [H5 [H4 [x0 [x1 [H6 [H7 [H8 H9]]]]]]]]] H3].
rewrite /= in H8.
by rewrite /= H8 in H3; destruct x0 => //.

Step (fun s h => exists l,
  exists y, y > 0 /\ [ var_e entry ]e_s = Z_of_nat y /\
    exists size'', size'' >= size /\
      (Heap_List l adr ** Array (y + 2) size'') s h /\
      In_hl l (y, size'', alloc) adr).

move: (split_verif2 _ _ H0 H) => H1.

Step TT. (* apply hoare_conseq (?) *)
- by apply hoare_prop_m.entails_id.
- rewrite /while.entails => {H1} s h [[x [H2 [H5 [H4 [x0 [x1 [H6 [H7 [H8 H9]]]]]]]]] H3].
  exists x; Resolve_topsy.
  exists x0, x1; by Resolve_topsy.

Step TT.
move=> s h [x [x0 [H2 [H4 [x1 [H3 [H6 H7]]]]]]].
rewrite /wp_assign; exists x; Resolve_topsy.
exists x0; Resolve_topsy.
exists x1; Resolve_topsy.
case_sepcon H6.
Compose_sepcon h1 h2.
by Resolve_topsy.
by Array_equiv.
Qed.

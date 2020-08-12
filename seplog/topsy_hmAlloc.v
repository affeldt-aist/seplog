(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ZArith_ext ssrnat_ext.
Require Import integral_type bipl seplog.
Require Import topsy_hm topsy_hmAlloc_prg.

Require Import expr_b_dp.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.
Import seplog_Z_m.

Local Close Scope positive_scope.
Local Open Scope heap_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_hoare_scope.

(** this file contains:
 - 1. the verification of list traversal (findFree)
 - 2. the verification of compaction (compact, original version and optimization)
 - 3. the verification of splitting (split)
 - 4. the verification of the allocation function (hmAlloc)
*)

Local Close Scope Z_scope.

Definition findFree_specif := forall adr x sizex size,
  size > 0 -> adr > 0 ->
  {{ fun s h => exists l, Heap_List l adr s h /\
     In_hl l (x, sizex, alloc) adr /\
     [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s }}
  findFree size entry fnd sz stts
  {{ fun s h => exists l, Heap_List l adr s h /\
     In_hl l (x, sizex, alloc) adr /\
     [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
     ((exists y size'', size'' >= size /\
      In_hl l (y, size'', topsy_hm.free) adr /\
      [ var_e entry \= nat_e y \&& nat_e y \> null ]b_s)
      \/
      [ var_e entry \= null ]b_s) }}.

Lemma findFree_verif : findFree_specif.
Proof.
rewrite /findFree_specif => adr x sizex size H H0.
rewrite /findFree.

(**  entry <- var_e hmStart; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\ [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\ [ var_e entry \= nat_e adr ]b_s ).

move: H1 => [l [Hl [Hl' Hb]]].
exists l.
by Resolve_topsy.

(**  stts <-* (entry -.> status); *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\ [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\ [ var_e entry \= nat_e adr ]b_s /\
  [ var_e stts \= Allocated \|| var_e stts \= Free ]b_s).

move: H1 => [x0 [H1 [H4 [H2 [H6 H5]]]]].
destruct x0 as [|p x0]; first by rewrite //= in H4.
destruct p.
exists (hlstat_bool2expr b).
apply mapsto_strictly_exact; split.
- case: H1 => h1 [h2 [H1 [H7 [H3 H9]]]].
  inversion_clear H3.
  + subst b nxt.
    case_sepcon H13.
    rewrite /= in H13_h31; case_sepcon H13_h31.
    Compose_sepcon h311 (h312 \U h32 \U h4 \U h2); last by done.
    rewrite /status; by Mapsto.
  + subst b nxt.
    rewrite /= in H13; case_sepcon H13.
    Compose_sepcon h31 (h32 \U h4 \U h2); last by done.
    rewrite /status; by Mapsto.
- exists ((n, b) :: x0).
  Resolve_topsy.
  destruct b; rewrite eval_b_upd_subst; by omegab.

(**  fnd <- cst_e 0%Z; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\ [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\ [ var_e entry \= nat_e adr ]b_s /\
  [ var_e stts \= Allocated \|| var_e stts \= Free ]b_s /\
  [ var_e fnd \= nat_e 0 ]b_s).

case: H1 => x0 [H1 [H4 [H2 [H7 [H6 H5]]]]].
exists x0.
by Resolve_topsy.

(**  while ((var_e entry \!= null) \&& (var_e fnd \!= cst_e 1%Z)) ( *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\ [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\
  (exists bloc_adr,
    [ var_e entry \= nat_e bloc_adr ]b_s /\
    ((bloc_adr = 0 /\ [ var_e fnd \= nat_e 0 ]b_s) \/
      (bloc_adr = get_endl l adr  /\
        [ var_e fnd \= nat_e 0 ]b_s /\
        bloc_adr > 0) \/
      (exists bloc_size bloc_status,
        bloc_adr > 0 /\
        In_hl l (bloc_adr, bloc_size, bloc_status) adr /\
        [ var_e fnd \= nat_e 0 ]b_s) \/
      exists bloc_size, bloc_size >= size /\
        In_hl l (bloc_adr, bloc_size, topsy_hm.free) adr /\
        [ var_e fnd \= nat_e 1 ]b_s /\
        bloc_adr > 0))).

rewrite /while.entails => s h [l [H1 [H4 [H2 [H8 [H7 [H6 H5]]]]]]].
exists l; Resolve_topsy.
case : l H1 H4 => [|[n b] tl] H1 H4; first by done.
exists adr; Resolve_topsy.
right; right; left; exists n, b; Resolve_topsy.
by rewrite /= !eqxx.

rewrite /while.entails => s h [[x0 [H2 [H3 [H4 [H5 [x1 [H6 H8]]]]]]] H1].
exists x0; Resolve_topsy.
case: H8.
- case => ? H7; subst x1.
  right; by omegab.
- case.
  + case => H7 [H8 H11].
    move: (get_endl_gt x0 adr) => H9.
    have H10 : [ var_e entry \!= null \&& var_e fnd \!= cst_e 1%Z ]b_s by omegab.
    rewrite /hoare_m.eval_b in H1.
    by rewrite H10 in H1.
  + case.
    * case => x2 [x3 [H8 [H9 H10]]].
      move: (get_endl_gt x0 adr) => H7.
      have H11 : [ var_e entry \!= null \&& var_e fnd \!= cst_e 1%Z ]b_s by omegab.
      rewrite /hoare_m.eval_b in H1.
      by rewrite H11 in H1.
    * move => [x2 [H7 [H10 [H11 H12]]]].
      left; exists x1, x2; by Resolve_topsy.

(**    stts <-* (entry -.> status); *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\ [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\
  (exists bloc_adr, [ var_e entry \= nat_e bloc_adr ]b_s /\
    ((bloc_adr = get_endl l adr /\
      [ var_e fnd \= nat_e O ]b_s /\
      [ var_e stts \= Allocated ]b_s /\
      bloc_adr > O) \/
    exists bloc_size bloc_status,
      In_hl l (bloc_adr, bloc_size, bloc_status) adr /\
      [ var_e fnd \= nat_e O ]b_s /\
      [ var_e stts \= hlstat_bool2expr bloc_status ]b_s /\
      bloc_adr > O))).

move: H1 => [[x0 [H2 [H5 [H3 [H6 [x1 [H4 H8]]]]]]] H9].
case: H8.
- case => H1 H7; subst x1.
  suff : False by done. omegab.
- case.
  + case => H1 [H7 H12].
    subst x1.
    exists Allocated.
    apply mapsto_strictly_exact; split.
    * move/hl_getstat_last : H2 => H2; case_sepcon H2.
      Compose_sepcon h1 h2; [rewrite /status; by Mapsto | done].
    * rewrite /wp_assign; exists x0.
      split; first by Heap_List_equiv.
      split; first by assumption.
      Resolve_topsy.
      exists (get_endl x0 adr).
      Resolve_topsy.
      left; by Resolve_topsy.
  + case.
    * case => x2 [x3 [H8 [H11 H1]]].
      case/In_hl_destruct : (H11) => [x4 [x5 [Hx0 H13]]].
      exists (hlstat_bool2expr x3).
      apply mapsto_strictly_exact; split.
      rewrite Hx0 in H2; move/hl_getstatus : H2 => H10; case_sepcon H10.
      Compose_sepcon h1 h2; [rewrite /status; by Mapsto | done].
      rewrite /wp_assign; exists x0.
      split; first by Heap_List_equiv.
      Resolve_topsy.
      exists (get_endl x4 adr); Resolve_topsy.
      right; exists x2, x3; Resolve_topsy.
      by rewrite H13.
      destruct x3; rewrite eval_b_upd_subst; omegab.
      by rewrite H13.
   * case => x2 [H1 [H11 [H13 H8]]].
     case/In_hl_destruct : (H11) => [x3 [x4 [H12 H14]]].
     exists Free.
     apply mapsto_strictly_exact; split.
     rewrite H12 in H2; move/hl_getstatus : H2 => H2; case_sepcon H2.
     Compose_sepcon h1 h2; [by Mapsto | done].
     rewrite /wp_assign; exists x0.
     split; first by Heap_List_equiv.
     split; first by assumption.
     Resolve_topsy.
     exists (get_endl x3 adr); Resolve_topsy.
     right; exists x2, topsy_hm.free; Resolve_topsy.
     by rewrite H14.
     by rewrite H14.

(**    ENTRYSIZE entry sz; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\ [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\
  (exists bloc_adr,
    [ var_e entry \= nat_e bloc_adr ]b_s /\
    ((bloc_adr = get_endl l adr /\
        [ var_e fnd \= nat_e 0 ]b_s /\
        [ var_e stts \= Allocated ]b_s /\
        bloc_adr > 0 /\
        [ var_e sz \= nat_e 0 ]b_s) \/
      exists bloc_size bloc_status,
        In_hl l (bloc_adr, bloc_size, bloc_status) adr /\
        [ var_e fnd \= nat_e 0 ]b_s /\
        [ var_e stts \= hlstat_bool2expr bloc_status ]b_s /\
        bloc_adr > 0 /\
        [ var_e sz \= nat_e bloc_size ]b_s))).

rewrite /ENTRYSIZE.

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\ [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s /\
  (exists bloc_adr, [ var_e entry \= nat_e bloc_adr ]b_s /\
    ((bloc_adr = get_endl l adr /\
      [ var_e fnd \= nat_e 0 ]b_s /\
      [ var_e stts \= Allocated ]b_s /\
      bloc_adr > 0 /\
      [ var_e sz \= nat_e 0 ]b_s ) \/
    (exists bloc_size bloc_status,
      In_hl l (bloc_adr, bloc_size, bloc_status) adr /\
      [ var_e fnd \= nat_e 0 ]b_s /\
      [ var_e stts \= hlstat_bool2expr bloc_status ]b_s /\
      bloc_adr > 0 /\
      [ var_e sz \= nat_e (bloc_adr + 2 + bloc_size) ]b_s)))).

move: H1 => [x0 [H1 [H4 [H2 [H5 [x1 [H7 H9]]]]]]].
case: H9.
- case => [H11 [H3 [H8 H10]]].
  exists null.
  apply mapsto_strictly_exact; split.
  move/hl_getnext_last : H1 => H1; case_sepcon H1.
  Compose_sepcon h1 h2; [rewrite /next; by Mapsto | done].
  rewrite /wp_assign; exists x0; Resolve_topsy.
  exists x1; Resolve_topsy.
  left; by Resolve_topsy.
- move => [x2 [x3 [H10 [H11 [H3 H8]]]]].
  move/In_hl_destruct : (H10) => [x4 [x5 [H9 H12]]].
  exists (nat_e (x1 + 2 + x2)).
  apply mapsto_strictly_exact; split.
  rewrite H9 in H1; move/hl_getnext : H1 => H6.
  case_sepcon H6.
  Compose_sepcon h1 h2; last by done.
  rewrite /next; by Mapsto.
  rewrite /wp_assign; exists x0; Resolve_topsy.
  exists (get_endl x4 adr); Resolve_topsy.
  right; exists x2, x3; split.
  by rewrite H12.
  Resolve_topsy.
  destruct x3; rewrite eval_b_upd_subst; by omegab.
  by rewrite H12.

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\ [ var_e hmStart \= nat_e adr ]b_s /\
  [ var_e result \= null ]b_s  /\
  (exists bloc_adr, [ var_e entry \= nat_e bloc_adr ]b_s /\
    ((bloc_adr = get_endl l adr /\
      [ var_e fnd \= nat_e 0 ]b_s /\
      [ var_e stts \= Allocated ]b_s /\
      bloc_adr > 0 /\
      [ var_e sz \= nat_e 0 \- nat_e bloc_adr \- nat_e 2 ]b_s) \/
    exists bloc_size bloc_status,
      In_hl l (bloc_adr, bloc_size, bloc_status) adr /\
      [ var_e fnd \= nat_e 0 ]b_s /\
      [ var_e stts \= hlstat_bool2expr bloc_status ]b_s /\
      bloc_adr > 0 /\
      [ var_e sz \= nat_e bloc_size ]b_s))).

move: H1 => [x0 [H1 [H4 [H2 [H5 [x1 [H7 H3]]]]]]].
case: H3.
- move => [H10 [H3 [H11 [H8 H9]]]].
  exists x0; Resolve_topsy.
  exists (get_endl x0 adr); Resolve_topsy.
  left; Resolve_topsy.
  by omegab.
- move => [x2 [x3 [H9 [H10 [H3 [H11 H8]]]]]].
  exists x0; Resolve_topsy.
  exists x1; Resolve_topsy.
  right; exists x2, x3; Resolve_topsy.
  rewrite eval_b_upd_subst; by destruct x3; omegab.

(**    ifte ((var_e stts \= Free) \&& (var_e sz \>= nat_e size)) thendo *)

Step TT.

Step TT.

move => s h [[x0 [H1 [H2 [H5 [H3 [x1 [H6 H8]]]]]]] H4].
case: H8.
- move => [H8 [H12 [H7 [H13 H10]]]].
  exists x0; Resolve_topsy.
  exists x1; Resolve_topsy.
  left; by Resolve_topsy.
- move => [x2 [x3 [H8 [H11 [H7 [H12 H9]]]]]].
  exists x0; Resolve_topsy.
  exists x1; Resolve_topsy.
  right; exists x2, x3; by Resolve_topsy.

Step TT.

rewrite /while.entails => s h [[x0 [H3 [H2 [H5 [H1 [x1 [H6 H8]]]]]]] H4].
exists x0; Resolve_topsy.
case: H8 => H7.
- move: H7 => [H12 [H7 [H13 [H10 H11]]]].
  have H8 : [ nat_e 0 \> var_e sz ]b_s by omegab.
  by rewrite H8 in H4.
- exists x1; by Resolve_topsy.

Step TT.

(*      (fnd <- cst_e 1%Z) *)

Step TT.

move => s h [[x0 [H2 [H5 [H3 [H6 [x1 [H8 H7]]]]]]] H9].
exists x0; split.
by apply Heap_List_inde_store with s.
Resolve_topsy.
exists x1; Resolve_topsy.
case: H7.
- move => [H4 [H12 [H1 [H13 H10]]]].
  suff : False by done. omegab.
- move => [x2 [[] [H11 [H1 [H12 [H10 H13]]]]]].
  + simpl hlstat_bool2expr in H12.
    right; right; right; exists x2.
    split; first by omegab.
    split; first by assumption.
    rewrite eval_b_upd_subst; by intuition.
  + suff : False by done. omegab.

(**    elsedo
         (entry <-* (entry -.> next))). *)

Step TT.

rewrite /while.entails => s h [[x0 [H2 [H5 [H1 [H6 [x1 [H8 H4]]]]]]] H3].
case: H4.
- move => [H11 [H7 [H12 [H9 H14]]]].
  exists (nat_e 0).
  apply mapsto_strictly_exact; split.
  move/hl_getnext_last : H2 => H2; case_sepcon H2.
  Compose_sepcon h1 h2; [rewrite /next; by Mapsto | done].
  rewrite /wp_assign.
  exists x0; split.
  by apply Heap_List_inde_store with s.
  Resolve_topsy.
  exists 0; Resolve_topsy.
  left; by Resolve_topsy.
- case => [x2 [x3 [H11 [H7 [H12 [H9 H13]]]]]].
  exists (nat_e (x1 + 2 +x2)).
  apply mapsto_strictly_exact; split.
  move/In_hl_destruct : H11 => [x4 [x5 [H15 H14]]].
  rewrite H15 in H2.
  move/hl_getnext : H2 => [h1 [h2 [H4 [H16 [H10 H17]]]]].
  Compose_sepcon h1 h2; last by done.
  rewrite /next; by Mapsto.
  rewrite /wp_assign.
  exists x0; split.
  by apply Heap_List_inde_store with s.
  Resolve_topsy.
  exists (x1 + 2 + x2); Resolve_topsy.
  move/In_hl_destruct : H11 => [x4 [x5 [H15 H14]]].
  case: x5 H15 => [|[n b] x5] H15.
  + right; left; split.
    by rewrite H15 get_endl_app H14.
    split.
    rewrite eval_b_upd_subst; by omegab.
    ssromega.
  + right; right; left; exists n, b.
    split; first by ssromega.
    split.
    rewrite H15; apply In_hl_or_app; right => /=.
    case: ifP => // _.
    by rewrite H14 /= !eqxx.
  by rewrite eval_b_upd_subst; omegab.
Qed.

Definition brk := 10.
Definition tmp := 11.
Definition cstts := 12.
Definition nstts := 13.

Definition compact'_specif:= forall adr size x sizex,
 size > 0 -> adr > 0 ->
  {{ fun s h => exists l, Heap_List l adr s h /\
     In_hl l (x, sizex, alloc) adr /\
     [ var_e hmStart \= nat_e adr \&& var_e result \= null \&& var_e cptr \= nat_e adr ]b_s }}
  compact' cptr nptr brk tmp cstts nstts
  {{ fun s h => exists l, Heap_List l adr s h /\
     In_hl l (x, sizex, alloc) adr /\
     [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s }}.

Lemma compact'_verif: compact'_specif.
Proof.
rewrite /compact'_specif /compact' => adr size x sizex H H0.

(**  while (var_e cptr \!= null) ( *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s  /\
  (exists cptr_value, [ var_e cptr \= nat_e cptr_value ]b_s /\
    (cptr_value = 0 \/
      cptr_value = get_endl l adr \/
      exists cptr_size cptr_status, In_hl l (cptr_value, cptr_size, cptr_status) adr))).

rewrite /while.entails => s h [x0 [H2 [H5 H6]]].
exists x0.
split; first by assumption.
split; first by assumption.
split; first by omegab.
exists adr.
split; first by omegab.
case: x0 H2 H5 => [| [n b] x0] H2 H5.
- by rewrite /= in H5.
- right; right; exists n, b => /=.
  by rewrite !eqxx.

rewrite /while.entails => s h [[x0 [H2 [H3 [H4 H5]]]] H6].
exists x0; by Resolve_topsy.

(**    nptr <-* (cptr -.> next); *)

Step (fun s h => exists l, Heap_List l adr s h /\
    In_hl l (x, sizex, alloc) adr /\
    [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
      (exists cptr_value nptr_value,
        [ var_e cptr \= nat_e cptr_value ]b_s /\
        [ var_e nptr \= nat_e nptr_value ]b_s /\
           ((cptr_value = get_endl l adr /\
             nptr_value = 0) \/
            exists cptr_size cptr_status,
               In_hl l (cptr_value, cptr_size, cptr_status) adr /\
               nptr_value = cptr_value + 2 + cptr_size))).

move: H1 => [[l [Hl [Hl' [Hs [cptr [Hs' [Hcptr' | [Hcptr' | [cptr_size [cptr_status Hl'']]]]]]]]]] Hcptr].
- subst cptr; by omegab.
- exists (nat_e 0).
  apply mapsto_strictly_exact; split.
  + move/hl_getnext_last : Hl => Hl; case_sepcon Hl.
    Compose_sepcon h1 h2; [rewrite /next; by Mapsto | done].
  + exists l; Resolve_topsy.
    exists cptr, 0; by Resolve_topsy.
- exists (nat_e (cptr + 2 + cptr_size)).
  apply mapsto_strictly_exact; split.
  move/In_hl_destruct : Hl'' => [x0 [x1 [H5 H6]]].
  rewrite H5 in Hl.
  move/hl_getnext : Hl => H4'.
  case_sepcon H4'.
  Compose_sepcon h1 h2; [rewrite /next; by Mapsto | done].
  exists l; Resolve_topsy.
  exists cptr, (cptr + 2 + cptr_size); Resolve_topsy.
  right; by exists cptr_size, cptr_status.

(*:    brk <- nat_e 1 ; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null \&& var_e brk \= nat_e 1 ]b_s /\
  (exists cptr_value nptr_value,
    [ var_e cptr \= nat_e cptr_value ]b_s /\
    [ var_e nptr \= nat_e nptr_value ]b_s /\
    ((cptr_value = get_endl l adr /\
      nptr_value = 0) \/
    exists cptr_size cptr_status,
      In_hl l (cptr_value,cptr_size,cptr_status) adr /\
      nptr_value = cptr_value + 2 + cptr_size))).

case: H1 => l [Hl [Hl' [Hb [cptr_value [nptr_value [Hcptr [Hnptr Htmp]]]]]]].
rewrite /wp_assign.
exists l; Resolve_topsy.
exists cptr_value, nptr_value; by Resolve_topsy.

(*:    cstts <-* (cptr -.> status); *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null \&& var_e brk \= nat_e 1 ]b_s /\
  (exists cptr_value nptr_value cstts_value,
    [ var_e cptr \= nat_e cptr_value ]b_s /\
    [ var_e nptr \= nat_e nptr_value ]b_s /\
        [ var_e cstts \= cstts_value ]b_s /\
        ((cptr_value = get_endl l adr /\
          nptr_value = 0 /\
          cstts_value = Allocated) \/
        exists cptr_size cptr_status,
          In_hl l (cptr_value,cptr_size,cptr_status) adr /\
          nptr_value = cptr_value + 2 + cptr_size /\
          cstts_value = (hlstat_bool2expr cptr_status)))).

case: H1 => l [Hl [Hl' [Hb [cptr_value [nptr_value [Hcptr [Hnptr []]]]]]]].
- case=> Hcptr_value Hnptr_value.
  exists Allocated.
  apply mapsto_strictly_exact; split.
  move/hl_getstat_last : Hl => Hl; case_sepcon Hl.
  Compose_sepcon h1 h2; [rewrite /status; by Mapsto | done].
  exists l; Resolve_topsy.
  exists cptr_value, nptr_value, Allocated; by Resolve_topsy.
- case=> cptr_size [cptr_status [Hl'' Hnptr_value]].
  exists (hlstat_bool2expr cptr_status).
  apply mapsto_strictly_exact; split.
  move/In_hl_destruct : Hl'' => [l1 [l2 [Hl1l2 Hcptr_value]]].
  rewrite Hl1l2 in Hl; move/hl_getstatus : Hl => Hl; case_sepcon Hl.
  Compose_sepcon h1 h2; [rewrite /status; by Mapsto | done].
  exists l; Resolve_topsy.
  exists cptr_value, nptr_value, (hlstat_bool2expr cptr_status); Resolve_topsy.
  by destruct cptr_status; Resolve_topsy.
  right; exists cptr_size, cptr_status; by Resolve_topsy.

(**    while ((var_e cstts \= Free) \&& (var_e nptr \!= null) \&& (var_e brk \= nat_e 1)) ( *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  ((exists cptr_value cptr_size brk_value,
    [ var_e cptr \= nat_e cptr_value ]b_s /\
    [ var_e nptr \= nat_e (cptr_value + 2 + cptr_size) ]b_s /\
    [ var_e cstts \= Free ]b_s /\
    [ var_e brk \= nat_e brk_value ]b_s /\
    In_hl l (cptr_value,cptr_size,topsy_hm.free) adr /\
    ((cptr_value + 2 + cptr_size = get_endl l adr /\ (brk_value = 0 \/ brk_value = 1)) \/
      (exists  nptr_size nptr_status,
        In_hl l (cptr_value + 2 + cptr_size,nptr_size,nptr_status) adr /\
        ((nptr_status = true /\ brk_value = 1) \/
          (nptr_status = false /\ (brk_value = 1 \/ brk_value = 0)))))) \/
  (exists cptr_value nptr_value cstts_value,
    [ var_e cptr \= nat_e cptr_value ]b_s /\
    [ var_e nptr \= nat_e nptr_value ]b_s /\
    [ var_e cstts \= Allocated ]b_s /\
    [ var_e brk \= nat_e 1 ]b_s /\
    ((cptr_value = get_endl l adr /\
      nptr_value = 0 /\
      cstts_value = Allocated) \/
    (exists cptr_size cptr_status,
      In_hl l (cptr_value,cptr_size,cptr_status) adr /\
      nptr_value = cptr_value + 2 + cptr_size))))).

case : H1 => x0 [H2 [H5 [H7 [x1 [x2 [x3 [H13 [H11 [H12 H10]]]]]]]]].
exists x0; Resolve_topsy.
case: H10.
- case => H4 [H13' Hx3]; subst x3.
  right; exists x1, x2, Allocated; by Resolve_topsy.
- case => x4 [[] [H4 [Hx2 Hx3]]]; subst x2 x3.
  + left; exists x1, x4, 1; Resolve_topsy.
    move/In_hl_destruct : H4 => [x2 [x3 [Hx0 Hx1]]].
    case : x3 Hx0 => [| [n b] x3] Hx0.
    * left; rewrite Hx0 get_endl_app /=; ssromega.
    * right; exists n, b.
      split; last by destruct b; Resolve_topsy.
      rewrite Hx0; apply In_hl_or_app; right => /=.
      have : get_endl x2 adr != x1 + 2 + x4 by apply/eqP; ssromega.
      move/negbTE => -> /=.
      by rewrite Hx1 !eqxx.
  + right; exists x1, (x1 + 2 + x4), Allocated; Resolve_topsy.
    right; by exists x4, false.

(**       nstts <-* (nptr -.> status); *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  (exists cptr_value cptr_size brk_value,
    [ var_e cptr \= nat_e cptr_value ]b_s /\
    [ var_e nptr \= nat_e (cptr_value + 2 + cptr_size) ]b_s /\
    [ var_e cstts \= Free ]b_s /\
    [ var_e brk \= nat_e brk_value ]b_s /\
    In_hl l (cptr_value,cptr_size,topsy_hm.free) adr /\
    ((cptr_value + 2 + cptr_size = get_endl l adr /\ (brk_value = 0 \/ brk_value = 1) /\
        [ var_e nstts \= Allocated ]b_s) \/
      exists  nptr_size nptr_status,
        In_hl l (cptr_value + 2 + cptr_size,nptr_size,nptr_status) adr /\
        ((nptr_status = true /\ brk_value = 1) \/
          (nptr_status = false /\ (brk_value = 1 \/ brk_value = 0))) /\
        [ var_e nstts \= hlstat_bool2expr nptr_status ]b_s))).

case : H1 => [[x0 [H3 [H6 [H7 H8]]]] H2].
case : H8.
- case => cptr_val [cptr_sz [brk_val [H12 [H13 [H14 [H15 [H17 H16]]]]]]].
  case: H16.
  + case => H15' H16.
    exists Allocated.
    rewrite /status.
    apply mapsto_strictly_exact; split.
    * move/hl_getstat_last : H3 => H3; case_sepcon H3.
      Compose_sepcon h1 h2; [by Mapsto | done].
    * rewrite /wp_assign; exists x0.
      Resolve_topsy.
      exists cptr_val, cptr_sz, brk_val; Resolve_topsy.
      left; by Resolve_topsy.
  + case => x4 [x5 [H15' H16]].
    exists (hlstat_bool2expr x5).
    rewrite /status.
    apply mapsto_strictly_exact; split.
    * case/In_hl_destruct : H15' => x6 [x7 [H17' H18]].
      rewrite H17' in H3; move/hl_getstatus : H3 => H3; case_sepcon H3.
      Compose_sepcon h1 h2; [rewrite H18 in H3_h1; by Mapsto | done].
    * rewrite /wp_assign; exists x0.
      Resolve_topsy.
      exists cptr_val, cptr_sz, brk_val; Resolve_topsy.
      right; exists x4, x5; by destruct x5; Resolve_topsy.
- case => cptr_val [nptr_val [cstts_val [H12 [H13 [H14 [H15 H16]]]]]].
  suff : False by done. omegab.

(**       ifte (var_e nstts \!= Free) thendo ( *)

Step TT.

(**          brk <- nat_e 0 *)

Step TT.
move=> s h H2.
case : H2 => [[x0 [H3 [H6 [H7 [x1 [x2 [x3 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]]]]] H4].
rewrite /wp_assign.
exists x0; Resolve_topsy.
left.
case: H13.
- case => H13 [H15 H16].
  exists x1, x2, 0; by Resolve_topsy.
- case => x4 [x5 [H13 [H15 H16]]].
  exists x1; exists x2, 0; Resolve_topsy.
  right; exists x4, x5; Resolve_topsy.
  destruct x5; omegab.

(**       ) elsedo (
	 tmp <-* nptr -.> next; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  (exists cptr_value cptr_size brk_value,
    [ var_e cptr \= nat_e cptr_value ]b_s /\
    [ var_e nptr \= nat_e (cptr_value + 2 + cptr_size) ]b_s /\
    [ var_e cstts \= Free ]b_s /\
    [ var_e brk \= nat_e brk_value ]b_s /\
    In_hl l (cptr_value, cptr_size, topsy_hm.free) adr /\
    exists nptr_size nptr_status,
      In_hl l (cptr_value + 2 + cptr_size, nptr_size, nptr_status) adr /\
      (nptr_status = true /\ brk_value = 1) /\
      [ var_e tmp \= nat_e (cptr_value + 2 + cptr_size + 2 + nptr_size) ]b_s)).

case : H1 => [[x0 [H3 [H6 [H7 [x1 [x2 [x3 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]]]]] H4].
case : H13.
- case => H13 [H15 H16].
  suff : False by done. omegab.
- case => x4 [x5 [H13 [H15 H16]]].
  destruct x5.
  + exists (nat_e (x1 + 2 + x2 + 2 + x4)).
    rewrite /next.
    apply mapsto_strictly_exact; split.
    * case/In_hl_destruct : H13 => x5 [x6 [H5 H17]].
      rewrite H5 in H3.
      move/hl_getnext : H3 => H14.
      case_sepcon H14.
      Compose_sepcon h1 h2; last by done.
      rewrite H17 in H14_h1; by Mapsto.
    * exists x0; Resolve_topsy.
      exists x1, x2, 1.
      case: H15 => [ [_ H14] | [] // ].
      subst x3;  Resolve_topsy.
      exists x4, true; by Resolve_topsy.
  + case: H15 => H5.
    * by case: H5.
    * suff : False by done. omegab.

(**         cptr -.> next *<- var_e tmp ; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  (exists cptr_value cptr_size,
    [ var_e cptr \= nat_e cptr_value ]b_s /\
    [ var_e cstts \= Free ]b_s /\
    [ var_e brk \= nat_e 1 ]b_s /\
    In_hl l (cptr_value, cptr_size, topsy_hm.free) adr /\
    [ var_e tmp \= nat_e (cptr_value + 2 + cptr_size) ]b_s)).

case : H1 => x0 [H2 [H5 [H6 [x1 [x2 [x3 [H10 [H11 [H12 [H13 [H14 [x4 [x5 [H15 [[H16 H18] H17]]]]]]]]]]]]]]].

case: (In_hl_next _ _ _ _ _ _ _ H14 H15) => x6 [x7 [H4 Hx1]].
subst x5 x3.
rewrite H4 /topsy_hm.free in H2.
case: (Heap_List_compaction x6 x7 x2 x4 _ s h H2) => x3 mem_s_h.
exists x3.
case_sepcon mem_s_h; Compose_sepcon h1 h2.
by rewrite /next; Mapsto.
move: mem_s_h_h2; apply monotony_imp => h' Hh'.
rewrite /next in Hh'; by Mapsto.
exists (x6 ++ (x2 + x4 + 2, topsy_hm.free) :: x7).
split; first by assumption.
split.
- rewrite H4 in H5.
  case/In_hl_app_or : H5 => H18.
  + by apply In_hl_or_app; left.
  + apply In_hl_or_app; right.
    move: H18.
    rewrite /= /alloc /topsy_hm.free /= -andbA andbC /= -andbA andbC /=.
    rewrite (_ : get_endl x6 adr + 2 + (x2 + x4 + 2) = get_endl x6 adr + 2 + x2 + 2 + x4) //; ssromega.
- Resolve_topsy.
  exists x1, (x2 + 2 + x4); Resolve_topsy.
  apply In_hl_or_app; right => /=.
  rewrite Hx1 (_ : x2 + x4 + 2 = x2 + 2 + x4) //; last by ssromega.
  by rewrite !eqxx.

(**         nptr <- (var_e tmp) *)

Step TT.
move=> s h H2.
rewrite /wp_assign.
case : H2 => x0 [H2 [H5 [H3 [x1 [x2 [H9 [H11 [H7 [H8 H6]]]]]]]]].
exists x0; Resolve_topsy.
left; exists x1, x2, 1; Resolve_topsy.
case/In_hl_destruct : H8 => x3 [x4 [Hx0 H13]].
case : x4 Hx0 => [|[n b] x4] Hx0.
- left; rewrite Hx0 get_endl_app /= H13; tauto.
- right; exists n, b; split.
  rewrite Hx0; apply In_hl_or_app; right => /=.
  case: ifP => // _.
  by rewrite H13 !eqxx.
destruct b; tauto.

(**       )
    );
    cptr <-* (cptr -.> next)
  ). *)

Step TT.
rewrite /while.entails; move=> s h [[x0 [H3 [H6 [H7 H8]]]] H4].
case : H8.
- case => x1 [x2 [x3 [H12 [H5 [H11 [H9 [H10 H14]]]]]]].
  case : H14.
  + case => H13 H14.
    rewrite /next.
    exists (nat_e (x1 + 2 + x2)).
    apply mapsto_strictly_exact; split.
    case/In_hl_destruct : H10 => x4 [x5 [H8 H16]].
    rewrite H8 in H3; move/hl_getnext : H3 => H2'.
    case_sepcon H2'; Compose_sepcon h1 h2; [by Mapsto | done].
    rewrite /wp_assign.
    exists x0; Resolve_topsy.
    exists (x1 + 2 + x2); by Resolve_topsy.
  + case => x4 [x5 [H13 H14]].
    rewrite /next.
    exists (nat_e (x1 + 2 + x2)).
    apply mapsto_strictly_exact; split.
    case/In_hl_destruct : H10 => x6 [x7 [H8 H16]].
    rewrite H8 in H3; move/hl_getnext : H3  => H2'.
    case_sepcon H2'; Compose_sepcon h1 h2; [by Mapsto | done].
    rewrite /wp_assign.
    exists x0; Resolve_topsy.
    exists (x1 + 2 + x2); Resolve_topsy.
    right; right; by exists x4, x5.
- case => x1 [x2 [x3 [H5 [H11 [H9 [H10 H13]]]]]].
  case: H13.
  + case => H12 [H14 H15].
    unfold next.
    exists (nat_e 0).
    apply mapsto_strictly_exact; split.
    move/hl_getnext_last : H3 => H3; case_sepcon H3.
    subst x1 x2 x3.
    Compose_sepcon h1 h2; [by Mapsto | done].
    rewrite /wp_assign.
    exists x0; Resolve_topsy.
    exists 0; by Resolve_topsy.
  + case => x4 [x5 [H12 H13]].
    exists (nat_e (x1 + 2 + x4)).
    unfold next.
    apply mapsto_strictly_exact; split.
    case/In_hl_destruct : H12 => x6 [x7 [H8 H15]].
    rewrite H8 in H3; move/hl_getnext : H3 => H2'.
    case_sepcon H2'; Compose_sepcon h1 h2; [by Mapsto | done].
    rewrite /wp_assign.
    exists x0; Resolve_topsy.
    exists (x1 + 2 + x4); Resolve_topsy.
    right.
    case/In_hl_destruct : H12 => x6 [x7 [H8 H15]].
    case: x7 H8 => [|[n b] x7] H8.
    * left; by rewrite H8 get_endl_app /= H15.
    * right; exists n, b.
      rewrite H8; apply In_hl_or_app; right => /=.
      have : get_endl x6 adr <> x1 + 2 + x4 by ssromega.
      move/eqP/negbTE => -> /=.
      rewrite (_ : get_endl x6 adr + 2 + x4 = x1 + 2 + x4); last by congruence.
      by rewrite !eqxx.
Qed.

Definition compact_specif := forall adr size sizex x,
  size > 0 -> adr > 0 ->
  {{ fun s h => exists l, Heap_List l adr s h /\
    In_hl l (x, sizex, alloc) adr /\
    [ var_e hmStart \= nat_e adr \&& var_e result \= null \&& var_e cptr \= nat_e adr ]b_s }}
  compact cptr nptr stts
  {{ fun s h => exists l, Heap_List l adr s h /\
    In_hl l (x, sizex, alloc) adr /\
    [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s }}.

Lemma compact_verif : compact_specif.
Proof.
unfold compact_specif.
intros.
unfold compact.

(**  while (var_e cptr \!= null) ( *)

Step (fun s h => exists l,
  Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists cur_adr, [ var_e cptr \= nat_e cur_adr ]b_s /\
    (cur_adr = 0 \/
      (cur_adr = get_endl l adr /\
        cur_adr > 0) \/
      (exists cur_size cur_status, In_hl l (cur_adr, cur_size, cur_status) adr /\
        cur_adr > 0))).

rewrite /while.entails => s h [x0 [H1 [H4 H3]]].
exists x0; Resolve_topsy.
exists adr.
split; first by omegab.
case: x0 H1 H4 => [| [n b] x0] H1 H4.
- by rewrite /= in H4.
- right; right; exists n, b; split; last by done.
  by rewrite /= !eqxx.

rewrite /while.entails => s h [[x0 [H2 [H3 [H4 H5]]]] H1].
exists x0; by Resolve_topsy.

(**    stts <-* (cptr -.> status); *)

Step (fun s h => exists l,
  Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists cur_adr, [ var_e cptr \= nat_e cur_adr ]b_s /\
    ((cur_adr = get_endl l adr /\
      cur_adr > 0 /\
      [ var_e stts \= Allocated ]b_s) \/
    (exists cur_size cur_status, In_hl l (cur_adr, cur_size, cur_status) adr /\
      [ var_e stts \= hlstat_bool2expr cur_status ]b_s /\
      cur_adr > 0))).

case : H1 => [[x0 [H2 [H4 [H5 [x1 [H8 H7]]]]]] H3].
case: H7 => [?|].
- subst x1; by omegab.
- case.
  + case => Hx1 H9.
    exists (nat_e 0).
    rewrite /status.
    apply mapsto_strictly_exact; split.
    move/hl_getstat_last : H2 => H2; case_sepcon H2.
    Compose_sepcon h1 h2; [by Mapsto | done].
    rewrite /wp_assign.
    exists x0; Resolve_topsy.
    exists x1; Resolve_topsy.
    left; by Resolve_topsy.
  + case => x2 [x3 [In_hl_x0 H9]].
    case/In_hl_destruct : (In_hl_x0) => x4 [x5 [H10 H11]].
    rewrite /status.
    exists (hlstat_bool2expr x3).
    apply mapsto_strictly_exact; split.
    * rewrite H10 in H2; move/hl_getstatus : H2 => H2; case_sepcon H2.
      Compose_sepcon h1 h2; [by Mapsto | done].
    * rewrite /wp_assign.
      exists x0; Resolve_topsy.
      exists x1; Resolve_topsy.
      right; exists x2, x3; Resolve_topsy.
      by destruct x3; Resolve_topsy.

(**    ifte (var_e stts \=  Free) thendo ( *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists cur_adr, [ var_e cptr \= nat_e cur_adr ]b_s /\
    ((cur_adr = get_endl l adr /\ cur_adr > 0 ) \/
    (exists cur_size cur_status, In_hl l (cur_adr, cur_size, cur_status) adr /\
      cur_adr > 0))).

(**      nptr <-* (cptr -.> next);  *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists cur_adr, [ var_e cptr \= nat_e cur_adr ]b_s /\
    (exists cur_size, In_hl l (cur_adr, cur_size, topsy_hm.free) adr /\
      [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s /\
      cur_adr > 0)).

case : H1 => [[x0 [H2 [H4 [H5 [x1 [H6 H7]]]]]] H3].
case : H7.
- case => H7 [H10 H11].
  suff : False by done. omegab.
- case => x2 [[] [H7 [H11 H10]]].
  + exists (nat_e (x1 + 2 + x2)).
    unfold next.
    apply mapsto_strictly_exact; split.
    * case/In_hl_destruct : H7 => x3 [x4 [Hx0 H9]].
      rewrite Hx0 in H2; move/hl_getnext : H2 => H12.
      case_sepcon H12; Compose_sepcon h1 h2; [by Mapsto | done].
    * rewrite /wp_assign.
      exists x0; Resolve_topsy.
      exists x1; Resolve_topsy.
      exists x2; by Resolve_topsy.
  + suff : False by done. omegab.

(**      stts <-* (nptr -.> status); *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists cur_adr, [ var_e cptr \= nat_e cur_adr ]b_s /\
    (exists cur_size, In_hl l (cur_adr, cur_size, topsy_hm.free) adr /\
      [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s /\
      cur_adr > 0 /\ (
        (exists next_size next_status,
          In_hl l ((cur_adr + 2 + cur_size), next_size, next_status) adr /\
          [ var_e stts \= hlstat_bool2expr next_status ]b_s) \/
        (cur_adr + 2 + cur_size = get_endl l adr /\
          [ var_e stts \= Allocated ]b_s)))).

case : H1 => x0 [H1 [H4 [H7 [x1 [H5 [x2 [H6 [H8 H9]]]]]]]].
case/In_hl_destruct : (H6) => x3 [x4 [H10 Hx1]].
case: x4 H10 => [|[n b] x4] H10.
- exists Allocated.
  rewrite /status.
  apply mapsto_strictly_exact; split.
  + rewrite H10 in H1; move/hl_getstat_last : H1 => H1; case_sepcon H1.
    Compose_sepcon h1 h2; last by done.
    rewrite get_endl_app in H1_h1; by Mapsto.
  + rewrite /wp_assign.
    exists x0; Resolve_topsy.
    exists x1; Resolve_topsy.
    exists x2; Resolve_topsy.
    right; Resolve_topsy.
    by rewrite -Hx1 H10 get_endl_app.
- exists (hlstat_bool2expr b).
  rewrite /status.
  apply mapsto_strictly_exact; split.
  + rewrite H10 in H1; Hl_getstatus H1 n H2; last by done.
    rewrite get_endl_app [get_endl _]/= in H2_h1; by Mapsto.
  + exists x0; Resolve_topsy.
    exists x1; Resolve_topsy.
    exists x2; Resolve_topsy.
    left; exists n, b; split.
    * rewrite H10; apply In_hl_or_app; right => /=.
      have : get_endl x3 adr <> x1 + 2 + x2 by ssromega.
      move/eqP/negbTE => -> /=.
      by rewrite Hx1 !eqxx.
    * by destruct b; Resolve_topsy.

(*:      while (var_e stts \= Free) ( *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists cur_adr, [ var_e cptr \= nat_e cur_adr ]b_s /\
    exists cur_size, In_hl l (cur_adr, cur_size, topsy_hm.free) adr /\
      [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s /\
      cur_adr > 0 /\ (
        (exists next_size next_status,
          In_hl l (cur_adr + 2 + cur_size, next_size, next_status) adr /\
          [ var_e stts \= hlstat_bool2expr next_status ]b_s) \/
        (cur_adr + 2 + cur_size = get_endl l adr /\
          [ var_e stts \= Allocated ]b_s))).

done.

(**        stts <-* (nptr -.> next); *)

rewrite /while.entails => s h [[x0 [H2 [H3 [H4 [x1 [H5 [x2 [H6 [H7 [H8 H9]]]]]]]]]] H1].
exists x0; Resolve_topsy.
exists x1; Resolve_topsy.
right; by exists x2, topsy_hm.free.

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists cur_adr, [ var_e cptr \= nat_e cur_adr ]b_s /\
    exists cur_size,  In_hl l (cur_adr, cur_size, topsy_hm.free) adr /\
      [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s /\
      cur_adr > 0 /\
      exists next_size,
        In_hl l (cur_adr + 2 + cur_size, next_size, topsy_hm.free) adr /\
        [ var_e stts \= nat_e (cur_adr + 2 + cur_size + 2 + next_size) ]b_s).

case : H1 => [[x0 [H2 [H4 [H5 [x1 [H6 [x2 [H7 [H8 [H9 H11]]]]]]]]]] H3].
case: H11.
- case => x3 [x4 [H11 H12]].
  destruct x4.
  + case/In_hl_destruct : (H11) => x4 [x5 [Hx0 H14]].
    exists (nat_e (x1 + 2 + x2 + 2 +x3)).
    rewrite /next.
    apply mapsto_strictly_exact; split.
    * rewrite Hx0 in H2; move/hl_getnext : H2 => H2.
      case_sepcon H2; Compose_sepcon h1 h2; [by Mapsto | done].
    * rewrite /wp_assign.
      exists x0; Resolve_topsy.
      exists x1; Resolve_topsy.
      exists x2; Resolve_topsy.
      exists x3; Resolve_topsy.
  + suff : False by done. omegab.
- case => H11 H12.
  suff : False by done. omegab.

(**        (cptr -.> next) *<- var_e stts; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists cur_adr, [ var_e cptr \= nat_e cur_adr ]b_s /\
    exists cur_size,
      In_hl l (cur_adr, cur_size, topsy_hm.free) adr /\
      cur_adr > 0 /\
      [ var_e stts \= nat_e (cur_adr + 2 + cur_size) ]b_s).

case : H1 => x0 [H1 [H4 [H5 [x1 [H6 [x2 [H7 [H8 [H9 [x3 [H10 H11]]]]]]]]]]].
case: (In_hl_next _ _ _ _ _ _ _ H7 H10) => x4 [x7 [H12 H13]].
rewrite /next.
rewrite H12 in H1; case/Heap_List_compaction : H1 => x5 H14.
case_sepcon H14.
exists x5.
Compose_sepcon h1 h2.
- by Mapsto.
- move: H14_h2; apply monotony_imp => h' Hh'; first by Mapsto.
  exists (x4 ++ (x2 + x3 + 2, topsy_hm.free) :: x7).
  split; first by done.
  split.
  * rewrite H12 in H4; case/In_hl_app_or : H4 => H4.
    - apply In_hl_or_app; by left.
    - apply In_hl_or_app; right.
      move: H4.
      rewrite /= /alloc /topsy_hm.free /= -andbA andbC /= -andbA andbC /=.
      rewrite (_ : get_endl _ adr + 2 + (x2 + x3 + 2) = get_endl x4 adr + 2 + x2 + 2 + x3) //; ssromega.
  * Resolve_topsy.
    exists x1; Resolve_topsy.
    exists (x2 + x3 + 2); split.
    - apply In_hl_or_app; right => /=.
      by rewrite -H13 !eqxx.
    - split; [assumption | omegab].

(*:        nptr <- var_e stts; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists cur_adr, [ var_e cptr \= nat_e cur_adr ]b_s /\
    exists cur_size,
      In_hl l (cur_adr, cur_size, topsy_hm.free) adr /\
      cur_adr > 0 /\
      [ var_e nptr \= nat_e (cur_adr + 2 + cur_size) ]b_s).

case : H1 => x0 [H1 [H4 [H5 [x1 [H6 [x2 [H8 [H9 H2]]]]]]]].
rewrite /wp_assign.
exists x0; Resolve_topsy.
exists x1; Resolve_topsy.
exists x2; by Resolve_topsy.

(*:        stts <-* (nptr -.> status))) *)

Step TT.

rewrite /while.entails => s h [x0 [H1 [H4 [H5 [x1 [H6 [x2 [H8 [H9 H2]]]]]]]]].
case/In_hl_destruct : (H8) => x3 [x4 [H10 H11]].
case : x4 H10 => [|[n b] x4] H10.
- exists Allocated.
  rewrite /status.
  apply mapsto_strictly_exact; split.
  + move/hl_getstat_last : H1 => H1; case_sepcon H1.
    rewrite H10 get_endl_app /= H11 in H1_h1.
    Compose_sepcon h1 h2; [by Mapsto | done].
  + rewrite /wp_assign.
    exists x0; Resolve_topsy.
    exists x1; Resolve_topsy.
    exists x2; Resolve_topsy.
    right; Resolve_topsy.
    by rewrite H10 get_endl_app H11.
- exists (hlstat_bool2expr b).
  rewrite /status.
  apply mapsto_strictly_exact; split.
  + rewrite H10 in H1; Hl_getstatus H1 n H3; last by done.
    rewrite get_endl_app [get_endl _]/= in H3_h1; by Mapsto.
  + rewrite /wp_assign.
    exists x0; Resolve_topsy.
    exists x1; Resolve_topsy.
    exists x2; Resolve_topsy.
    left; exists n, b; split.
    * rewrite H10; apply In_hl_or_app; right => /=.
      have : get_endl x3 adr <> x1 + 2 + x2 by ssromega.
      move/eqP/negbTE => -> /=.
      by rewrite H11 !eqxx.
    * by destruct b; Resolve_topsy.

(**    elsedo
      skip; *)

Step TT.
rewrite /while.entails => s h [[x0 [H2 [H5 [H7 [x1 [H6 H8]]]]]] H3].
exists x0; Resolve_topsy.
exists x1; Resolve_topsy.
case: H8.
- left; tauto.
- case => x2 [x3 [H11 [H10 H12]]].
  right; exists x2, x3; by Resolve_topsy.

(**      cptr <-* (cptr -.> next)). *)

Step TT.
rewrite /while.entails => s h [x0 [H1 [H4 [H2 [x1 [H5 H6]]]]]].
rewrite /next.
case: H6.
- case => H6 H8.
  exists (nat_e 0).
  apply mapsto_strictly_exact; split.
  move/hl_getnext_last : H1 => H3; case_sepcon H3.
  Compose_sepcon h1 h2; [by Mapsto | done].
  rewrite /wp_assign.
  exists x0; Resolve_topsy.
  exists 0; by Resolve_topsy.
- case => x2 [x3 [H6 H8]].
  case/In_hl_destruct : H6 => x4 [x5 [H9 Hx1]].
  exists (nat_e (x1 + 2 + x2)).
  apply mapsto_strictly_exact; split.
  + rewrite H9 in H1; move/hl_getnext : H1 => H3.
    case_sepcon H3; Compose_sepcon h1 h2; [by Mapsto | done].
  + rewrite /wp_assign.
    exists x0; Resolve_topsy.
    exists (x1 + 2 + x2); Resolve_topsy.
    case : x5 H9 => [|[n b] x5] H9.
    * right; left.
      rewrite H9 get_endl_app Hx1 /=; ssromega.
    * right; right; exists n, b.
      split; last by ssromega.
      rewrite H9; apply In_hl_or_app; right => /=.
      have : get_endl x4 adr <> x1 + 2 + x2 by ssromega.
      move/eqP/negbTE => -> /=.
      by rewrite Hx1 !eqxx.
Qed.

Definition split_specif := forall adr size sizex x,
  size > 0 -> adr > 0 ->
  {{ fun s h => exists l, Heap_List l adr s h /\
     In_hl l (x, sizex, alloc) adr /\
     [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
     exists y size'', size'' >= size /\
       In_hl l (y, size'', topsy_hm.free) adr /\
       [ var_e entry \= nat_e y ]b_s /\
       y > 0 /\ y <> x }}
  split entry size cptr sz
  {{ fun s h => exists l, In_hl l (x, sizex, alloc) adr /\
     exists y, y > 0 /\ [ var_e entry \= nat_e y ]b_s /\
       exists size'', size'' >= size /\
         (Heap_List l adr ** Array (y + 2) size'') s h /\
         In_hl l (y, size'', alloc) adr /\ y <> x }}.

Lemma split_verif : split_specif.
Proof.
rewrite /split_specif.
intros.
rewrite /split.

(**  ENTRYSIZE entry sz; *)

rewrite /ENTRYSIZE /LEFTOVER.

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists y size'', size'' >= size /\
    In_hl l (y, size'', topsy_hm.free) adr /\
    [ var_e entry \= nat_e y ]b_s /\
    y > 0 /\ y <> x /\
    [ var_e sz \= nat_e size'' ]b_s).

Step (fun s h => exists l, Heap_List l adr s h /\
    In_hl l (x, sizex, alloc) adr /\
    [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
    exists y size'', size'' >= size /\
     In_hl l (y, size'', topsy_hm.free) adr /\
     [ var_e entry \= nat_e y ]b_s /\
     y > 0 /\ y <> x /\
     [ var_e sz \= nat_e (y + 2 + size'') ]b_s).

case : H1 => x0 [H1 [H4 [H2 [x1 [x2 [H7 [H8 [H10 [H6 H5]]]]]]]]].
exists (nat_e (x1 + 2 + x2)).
rewrite /next.
apply mapsto_strictly_exact; split.
case/In_hl_destruct : H8 => x3 [x4 [H11 H12]].
rewrite H11 in H1; move/hl_getnext : H1 => H2'.
case_sepcon H2'; Compose_sepcon h1 h2; [by Mapsto | done].
rewrite /wp_assign.
exists x0; Resolve_topsy.
exists x1, x2; by Resolve_topsy.

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists y size'', size'' >= size /\
     In_hl l (y, size'', topsy_hm.free) adr /\
     [ var_e entry \= nat_e y ]b_s /\
     y > 0 /\ y <> x /\
     [ var_e sz \= nat_e size'' ]b_s).

case : H1 => x0 [H1 [H4 [H2 [x1 [x2 [H7 [H8 [H10 [H6 [H5 H9]]]]]]]]]].
rewrite /wp_assign.
exists x0; Resolve_topsy.
exists x1, x2; by Resolve_topsy.

Step TT.

Step TT.

move=> s h [[x0 [H1 [H4 [H2 [x1 [x2 [H7 [H8 [H10 [H6 [H5 H9]]]]]]]]]]] H1'].
suff : False by done. omegab.

Step TT.

rewrite /while.entails => *; tauto.

(**  ifte (var_e sz \>= (nat_e size \+ nat_e LEFTOVER \+ nat_e 2)) thendo ( *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists y size'', size'' >= size /\
    In_hl l (y, size'', topsy_hm.free) adr /\
    [ var_e entry \= nat_e y ]b_s /\
    y > 0 /\ y <> x).

(**    cptr <- var_e entry \+ nat_e 2 \+ nat_e size; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists y size'', size'' >= size /\
    In_hl l (y, size'', topsy_hm.free) adr /\
    [ var_e entry \= nat_e y ]b_s /\
    y > 0 /\ y <> x /\
    [ var_e sz \= nat_e size'' ]b_s /\
    size'' >= size + LEFTOVER + 2 /\
    [ var_e cptr \= nat_e (y + 2 + size) ]b_s).

unfold LEFTOVER.
case : H1 => [[x0 [H1 [H4 [H2 [x1 [x2 [H7 [H8 [H10 [H6 [H5 H9]]]]]]]]]]] H1'].
rewrite /wp_assign.
exists x0; Resolve_topsy.
exists x1, x2; Resolve_topsy; by omegab.

(*:    sz <-* (entry -.> next); *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  exists y size'', size'' >= size /\
    In_hl l (y, size'', topsy_hm.free) adr /\
    [ var_e entry \= nat_e y ]b_s /\
    y > 0 /\ y <> x /\
    [ var_e sz \= nat_e (y + 2 + size'') ]b_s /\
    size'' >= size + LEFTOVER + 2 /\
    [ var_e cptr \= nat_e (y + 2 + size) ]b_s).

case : H1 => x0 [H1 [H4 [H2 [x1 [x2 [H7 [H8 [H9 [H11 [H12 [H13 [H14 H15]]]]]]]]]]]].
exists (nat_e (x1 + 2 + x2)).
rewrite /next.
apply mapsto_strictly_exact; split.
case/In_hl_destruct : H8 => x3 [x4 [Hx0 Hx1]].
rewrite Hx0 in H1; move/hl_getnext : H1 => H2'.
case_sepcon H2'; Compose_sepcon h1 h2; [by Mapsto | done].
rewrite /wp_assign.
exists x0; Resolve_topsy.
by exists x1, x2; Resolve_topsy.

(**    (cptr -.> next) *<- var_e sz; *)

Step (fun s h => exists e'',
  (cptr -.> status |~> e'' **
    (cptr -.> status |~> Free -*
      (fun s0 h0 => exists e''0,
        (entry -.> next |~> e''0 **
          (entry -.> next |~> var_e cptr -*
            (fun s1 h1 => exists l, Heap_List l adr s h1 /\
              In_hl l (x, sizex, alloc) adr /\
              [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s1 /\
              exists y size'',
                size'' >= size /\
                In_hl l (y, size'', topsy_hm.free) adr /\
                [ var_e entry \= nat_e y ]b_s1 /\
                y > 0 /\ y <> x))) s0 h0))) s h).

case : H1 => x0 [H1 [H2 [H3 [x1 [x2 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]]]]]].
rewrite (_ : x2 = size + 2 + (x2 - 2 - size)) in H5; last by ssromega.
case/In_hl_destruct : H5 => x3 [x4 [H3' H15]].
rewrite H3' in H1; case/Heap_List_splitting : H1 => x5 H16.
exists x5.
case_sepcon H16.
rewrite /next.
Compose_sepcon h1 h2.
  rewrite H15 in H16_h1; by Mapsto.
rewrite /status.
move: H16_h2; apply assert_m.monotony_imp.
  move=> h' Hh'; by Mapsto.
move=> h' Hh'.
case: Hh' => x6 H18.
exists x6.
case_sepcon H18.
Compose_sepcon h'1 h'2; first by Mapsto.
move: H18_h'2; apply monotony_imp.
  move=> h'' Hh''; by Mapsto.
move=> h'' Hh''.
case: Hh'' => x7 H21.
exists x7.
case_sepcon H21.
Compose_sepcon h''1 h''2; first by Mapsto.
move: H21_h''2; apply monotony_imp.
  move=> h''' Hh'''; by Mapsto.
move=> h''' Hh'''.
exists (x3 ++ (size, true) :: (x2 - 2 - size, true) :: x4).
split; first by assumption.
Resolve_topsy.
- rewrite H3' in H2; case/In_hl_app_or : H2 => H2.
  - apply In_hl_or_app; by left.
  - apply In_hl_or_app; right.
    move: H2.
    do 2 rewrite /= /alloc /topsy_hm.free /= -andbA andbC /=.
    by rewrite !addnA.
exists x1, size; Resolve_topsy.
apply In_hl_or_app; right => /=.
by rewrite H15 !eqxx.

(*:    (cptr -.> status) *<- Free; *)

Step (fun s0 h0 => exists e'',
  (entry -.> next |~> e'' **
    (entry -.> next |~> var_e cptr -*
      (fun s h => exists l,
        Heap_List l adr s h /\
        In_hl l (x, sizex, alloc) adr /\
        [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
        exists y size'', size'' >= size /\
          In_hl l (y, size'', topsy_hm.free) adr /\
          [ var_e entry \= nat_e y ]b_s /\
          y > 0 /\ y <> x))) s0 h0).

assumption.

(**    (entry -.> next) *<- var_e cptr) *)

Step TT.
by apply hoare_prop_m.entails_id.

(**   elsedo
     skip *)

Step TT.
rewrite /while.entails => s h [[x0 [H1 [H4 [H2 [x1 [x2 [H7 [H8 [H10 [H6 [H5 H9]]]]]]]]]]] H1'].
exists x0; Resolve_topsy.
exists x1, x2; by Resolve_topsy.

(**  (entry -.> status) *<- Allocated. *)

Step TT.
rewrite /while.entails => s h [x0 [H1 [H2 [H3 [x1 [x2 [H4 [H5 [H6 [H7 H8]]]]]]]]]].
case/In_hl_destruct : H5 => x3 [x4 [H11 H12]].
rewrite H11 in H1; case/hl_free2alloc : H1 => x5 H1.
case_sepcon H1.
exists x5.
rewrite /status.
Compose_sepcon h1 h2; first by Mapsto.
move: H1_h2; apply monotony_imp => h' Hh'; first by Mapsto.
case_sepcon Hh'.
exists (x3 ++ (x2,false) :: x4).
Resolve_topsy.
- rewrite H11 in H2; case/In_hl_app_or : H2 => H2.
  - apply In_hl_or_app; by left.
  - rewrite /= /alloc /topsy_hm.free /= -andbA andbC /= in H2.
    apply In_hl_or_app; right => /=.
    have : get_endl x3 adr <> x by lia.
    by move/eqP/negbTE => ->.
- exists x1; Resolve_topsy.
  exists x2; Resolve_topsy.
  Compose_sepcon h'1 h'2; [done | by Array_equiv].
  apply In_hl_or_app; right.
  by rewrite /= H12 !eqxx.
Qed.

Definition hmAlloc_specif := forall adr x sizex size, adr > 0 -> size > 0 ->
  {{ fun s h => exists l, Heap_List l adr s h /\
    In_hl l (x, sizex, alloc) adr /\
    [ var_e hmStart \= nat_e adr ]b_s }}
  hmAlloc result size entry cptr fnd stts nptr sz
  {{ fun s h =>
    (exists l y, y > 0 /\ [ var_e result \= nat_e (y + 2) ]b_s /\
      exists size'', size'' >= size /\
        (Heap_List l adr ** Array (y + 2) size'') s h /\
        In_hl l (x, sizex, alloc) adr /\ In_hl l (y, size'', alloc) adr /\
        x <> y)
    \/
    (exists l, [ var_e result \= nat_e 0 ]b_s /\
      Heap_List l adr s h /\ In_hl l (x, sizex, alloc) adr) }}.

Lemma hmAlloc_verif: hmAlloc_specif.
Proof.
rewrite /hmAlloc_specif /hmAlloc => adr x sizex size H H0.

(**  result <- null; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s).

case : H1 => x0 [H1 [H4 H5]].
rewrite /wp_assign.
exists x0; by Resolve_topsy.

(**  findFree size entry fnd sz stts; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  ((exists y size'',
    size'' >= size /\
    In_hl l (y, size'', topsy_hm.free) adr /\
    [ (var_e entry \= nat_e y) ]b_s /\
    y > 0) \/
  [ var_e entry \= null ]b_s)).

move: (findFree_verif adr x sizex size H0 H) => H1.

Step TT. (* apply hoare_conseq (?) *)
- rewrite /while.entails => s h [x0 [H2 [H4 [H3 H6]]]] {H1}.
  exists x0; Resolve_topsy.
  case : H6 => H1.
  + case : H1 => x1 [x2 [H5 [H7 H1]]].
    left; exists x1, x2; Resolve_topsy.
    omegab.
  + by right.
- by apply hoare_prop_m.entails_id.

(**  ifte (var_e entry \= null) thendo ( *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s /\
  ((exists y size'', size'' >= size /\
    In_hl l (y, size'', topsy_hm.free) adr /\
    [ var_e entry \= nat_e y ]b_s /\
    y > 0) \/ [ var_e entry \= null ]b_s)).

(**    cptr <- var_e hmStart; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr ]b_s /\ [ var_e result \= null ]b_s /\
  [ var_e entry \= null ]b_s /\ [ var_e cptr \= var_e hmStart ]b_s).

case : H1 => [[x0 [H2 [H5 [H4 H7]]]] H6].
case : H7.
- case => x1 [x2 [H7 [H9 [H11 H8]]]].
  suff : False by done. omegab.
- exists x0; by Resolve_topsy.

(**    compact cptr nptr stts; *)

Step (fun s h => exists l, Heap_List l adr s h /\
  In_hl l (x, sizex, alloc) adr /\
  [ var_e hmStart \= nat_e adr \&& var_e result \= null ]b_s).

move: (compact_verif adr size sizex x H0 H) => H1.
Step TT.
- rewrite /while.entails => {H1} s h [x0 [H1 [H4 H2]]].
  exists x0; by Resolve_topsy.
- rewrite /while.entails => s h [x0 [H2 [H5 [H9 [H7 [H6 H4]]]]]].
  exists x0; by Resolve_topsy.

move: (findFree_verif adr x sizex size H0 H) => H1.

(**    findFree size entry fnd sz stts *)

Step TT. (* apply hoare_conseq (?) *)
- rewrite /while.entails => s h [x0 [H2 [H5 [H7 H3]]]].
  exists x0; Resolve_topsy.
  case : H3 => H4.
  + case : H4 => x1 [x2 [H3 [H8 H4]]].
    left; exists x1, x2; Resolve_topsy.
    by omegab.
  + by right.
- done.

(**  ) elsedo
       skip *)

Step TT.
rewrite /while.entails; intros; tauto.

(**  ifte (var_e entry \= null) thendo ( *)

Step TT.

(**    result <- HM_ALLOCFAILED *)

Step TT.
move=> s h H1.
rewrite /wp_assign.
case : H1 => [[x0 [H2 [H5 [H3 H7]]]] H4].
case : H7 => H1.
- case : H1 => x1 [x2 [H7 [H9 [H11 H8]]]].
  suff : False by done. omegab.
- right; exists x0; by Resolve_topsy.

(**  ) elsedo (
    split entry size cptr sz; *)

Step (fun s h => exists l y, y > 0 /\
  [ var_e entry \= nat_e y ]b_s /\
  exists size', size' >= size /\
    (Heap_List l adr ** Array (y + 2) size') s h /\
    In_hl l (x, sizex, alloc) adr /\
    In_hl l (y, size', alloc) adr /\ x <> y).

move: (split_verif adr size sizex x H0 H) => H1.

Step TT. (* apply hoare_conseq (?) *)
- rewrite /while.entails => {H1} s h [x0 [H1 [x1 [H2 [H3 [x2 [H4 [H5 [H6 H7]]]]]]]]].
  exists x0, x1; Resolve_topsy.
  exists x2; by Resolve_topsy.
- rewrite /while.entails => {H1} s h [[x0 [H2 [H5 [H7 H1]]]] H3].
  case : H1 => H4.
  + case: H4 => x1 [x2 [H8 [H9 H11]]].
    exists x0; Resolve_topsy.
    exists x1, x2; Resolve_topsy.
    tauto.
    omegab.
    by apply (In_hl_dif _ _ _ _ _ _ H5 H9).
  + by omegab.

(**    result <- var_e entry \+ nat_e 2
     ). *)

Step TT.
rewrite /wp_assign => s h [x0 [x1 [H2 [H3 [x2 [H4 [H5 [H6 [H7 H8]]]]]]]]].
left; exists x0, x1; Resolve_topsy.
exists x2; Resolve_topsy.
case_sepcon H5.
Compose_sepcon h1 h2.
by Resolve_topsy.
by Array_equiv.
Qed.

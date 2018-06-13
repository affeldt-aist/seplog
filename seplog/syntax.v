(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Permutation.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ssrnat_ext seq_ext.
Require Import bipl seplog integral_type.

Module Syntax (A : IntegralType).

Module Import seplog_m := Seplog A.
Import seplog_m.assert_m.expr_m.
Import seplog_m.assert_m.

Local Open Scope Z_scope.
Local Open Scope seplog_expr_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_assert_scope.
Local Open Scope seplog_hoare_scope.

Fixpoint contains_malloc (c : @while.cmd cmd0 expr_b) : bool :=
  match c with
    | skip => false
    | _ <- _ => false
    | _ <-* _ => false
    | _ *<- _ => false
    | malloc _ _ => true
    | free _ => false
    | while.while _ c => contains_malloc c
    | c ; d => contains_malloc c || contains_malloc d
    | while.ifte _ c d => contains_malloc c || contains_malloc d
  end.

Lemma no_malloc_heap_invariant0 s c s' :
  s -- c ----> s' ->
  ~~ contains_malloc c ->
  forall st st' h',
    s = Some (st, heap.emp) ->
    s' = Some (st', h') ->
    h' = heap.emp.
Proof.
elim=> //=; clear s c s'.
move=> [s h] _ st st' h' [] X Y [] U V; by subst.
move=> s h x e _ st st' h' [] X Y [] U V; by subst.
move=> s h c e p v H st st' h' [] X Y [] U V; by subst.
move=> s h e e' p v H H1 _ st st' h' [] X Y [] U V; subst.
by apply heap.upd_emp.
move=> s h e v p H H1 _ st st' h' [] X Y [] U V; subst.
by apply heap.dif_emp.
Qed.

Lemma no_malloc_heap_invariant : forall s c s', s -- c ---> s' ->
  ~~ contains_malloc c ->
  forall st st' h', s = Some (st, heap.emp) -> s' = Some (st', h') ->
    h' = heap.emp.
Proof.
move=> s c s'.
elim=> //; clear s c s'.
- by apply no_malloc_heap_invariant0.
- move=> s s' s'' c d Hc IHc Hd IHd /=.
  case/norP => H1 H2 st st' h' X Y.
  destruct s' as [[si hi]|].
  move: {IHc}(IHc H1 st si hi X (refl_equal _)) => IHc.
  move: {IHd}(IHd H2 si st' h') => IHd.
  subst hi.
  by move: {IHd}(IHd (refl_equal _) Y).
  move/semop_prop_m.from_none : Hd => Hd; by subst s''.
- move=> s s' b c d Hb Hc IH /=.
  case/norP => H1 H2 st st' h' [] ? Hs'; subst.
  by eapply IH; eauto.
- move=> s s' b c d Hb Hc IH /=.
  case/norP=> H1 H2 st st' h' [] ? Hs'; subst.
  by eapply IH; eauto.
- move=> s s' s'' b c Hb Hc IH Hwhile IHwhile Hnomalloc st st' h' [] X Y; subst.
  destruct s' as [[si hi]|].
  move: {IH}(IH Hnomalloc st si hi (refl_equal _) (refl_equal _)) => IH.
  subst hi.
  by move: {IHwhile}(IHwhile Hnomalloc si st' h' (refl_equal _) (refl_equal _)).
  by move/semop_prop_m.from_none : Hwhile.
- move=> s b c _ _ st st' h' [] -> [] ? ?; by subst.
Qed.

Lemma var_unchanged0' s c s' : (s -- c ----> s') ->
  forall st h st' h', s = Some (st, h) -> s' = Some (st', h') ->
  forall x, ~ x \in seplog_m.modified_vars c ->
    [ x ]_ st = [ x ]_ st'.
Proof.
case=> //; clear s c s'.
- move=> [s h] s_ h_ s' h' [] <- _ [] <- _ x _ //.
- move=> s h x e s_ h_ s' h' [] <- _ [] <- _ x0 Hx0.
  rewrite assert_m.expr_m.store.get_upd //.
  rewrite /= mem_seq1 in Hx0.
  by apply/negP.
- move=> s h x e z Hz s_ h_ s' h' [] <- _ [] <- _ x0 Hx0.
  rewrite assert_m.expr_m.store.get_upd //.
  rewrite /= mem_seq1 in Hx0.
  by apply/negP.
- by move=> s h e e' p z Hp Hz s_ h_ s' h' [] <- _ [] <- _ x0 Hx0.
- move=> s h x e n Hn s_ h_ st' h' [] <- _ [] <- _ x0 Hx0 //.
  rewrite assert_m.expr_m.store.get_upd //.
  rewrite /= mem_seq1 in Hx0.
  by apply/negP.
- by move=> s h e z p Hp Hz s_ h_ s' h' [] <- _ [] <- _ x0 Hx0.
Qed.

Lemma var_unchanged' s c s' : (s -- c ---> s') ->
  forall st h st' h', s = Some (st, h) -> s' = Some (st', h') ->
  forall x, ~ x \in seplog_m.modified_vars c ->
    [ x ]_ st = [ x ]_ st'.
Proof.
elim=> //; clear s c s'.
- exact var_unchanged0'.
- move=> s s' s'' c1 c2 Hc1 IHc1 Hc2 IHc2 st h st'' h'' Hs Hs'' x0 Hx0.
  destruct s' as [[st' h']|].
  apply trans_eq with ([ x0 ]_ st').
  eapply IHc1.
  apply Hs.
  reflexivity.
  contradict Hx0.
  by rewrite /= mem_cat Hx0.
  eapply IHc2.
  reflexivity.
  apply Hs''.
  contradict Hx0.
  by rewrite /= mem_cat Hx0 orbT.
  destruct s'' as [|] => //.
  by move/semop_prop_m.from_none : Hc2.
- move=> st s' b c1 c2 Hb Hc1 IHc1 st_ h_ st' h' [] Hst Hs' x Hx.
  eapply IHc1.
  rewrite Hst; reflexivity.
  apply Hs'.
  contradict Hx.
  rewrite /= in Hx *.
  by rewrite mem_cat Hx.
- move=> [st h] s' b c1 c2 Hb Hc1 IHc1 st_ h_ st' h' [] <- _ Hs' x Hx.
  eapply IHc1.
  reflexivity.
  apply Hs'.
  contradict Hx.
  rewrite /= in Hx *.
  by rewrite mem_cat Hx orbT.
- move=> [st h] s' s'' b c Hb Hc IHc Hwhile IHwhile st_ h_ st'' h'' [] <- _ Hs'' x Hx.
  destruct s' as [[st' h']|].
  apply trans_eq with ([ x ]_ st').
  eapply IHc.
  reflexivity.
  reflexivity.
  by contradict Hx.
  eapply IHwhile.
  reflexivity.
  apply Hs''.
  done.
  destruct s'' as [|] => //.
  by move/semop_prop_m.from_none : Hwhile.
- by move=> [st h] b c Hb st_ h_ st' h' [] <- _ [] <- _ x Hx.
Qed.

Lemma var_unchanged st h c st' h' : Some (st, h) -- c ---> Some (st', h') ->
  forall x, ~ x \in seplog_m.modified_vars c ->
    [ x ]_ st = [ x ]_ st'.
Proof. move=> Hc x Hx. eapply var_unchanged'; eauto. Qed.

Lemma exec0_deter st (c : cmd0) st' : st -- c ----> st' ->
  ~~ contains_malloc c ->
  forall st'', st -- c ----> st'' -> st' = st''.
Proof.
elim=> //; clear st c st'.
- move=> [s h] Hc [[s' h']|]; by inversion 1.
- move=> s h x e Hc [[s' h']|].
  + inversion 1; by subst.
  + by inversion 1.
- move=> s h x e v Hv Hc [[s' h']|].
  + inversion 1; subst.
    rewrite H1 in Hv; case: Hv => X; by subst v0.
  + inversion 1; subst.
    by rewrite H1 in Hv.
- move=> s h x e Hv Hc [[s' h']|] //.
  inversion 1; subst.
  by rewrite H1 in Hv.
- move=> s h e e' p v Hp Hv Hc [[s' h']|].
  + inversion 1; by subst.
  + inversion 1; subst.
    by rewrite H5 in Hv.
- move=> s h e e' p Hp Hv Hc [[s' h']|] //.
  inversion 1; subst.
  by rewrite H7 in Hv.
- move=> s h e v p Hp Hv Hc [[s' h']|].
  + inversion 1; by subst.
  + inversion 1; subst.
    by rewrite H4 in Hv.
- move=> s h e p Hp Hv Hc [[s' h']|] //.
  inversion 1; subst.
  by rewrite H6 in Hv.
Qed.

Lemma exec_deter ST c ST' : ST -- c ---> ST' ->
  ~~ contains_malloc c ->
  forall ST'', ST -- c ---> ST'' -> ST' = ST''.
Proof.
induction 1 => Hc st'' H'.
- symmetry; apply semop_prop_m.from_none with c => //.
- inversion H'; subst.
  apply semop_prop_m.from_none with c => //.
  apply while.exec_cmd0 => //.
  eapply exec0_deter; eauto.
- (* seq *) inversion H'; subst.
  + apply semop_prop_m.from_none in H; subst s'.
    by apply semop_prop_m.from_none in H0.
  + have X : s' = s'0.
      apply IHexec1 => //.
      rewrite /= negb_or in Hc.
      by case/andP : Hc.
    subst s'0.
    apply IHexec2 => //.
    rewrite /= negb_or in Hc.
    by case/andP : Hc.
- (* ifte true *) inversion_clear H' => //.
  apply IHexec => //.
  rewrite /= negb_or in Hc.
  by case/andP : Hc.
  by rewrite H in H1.
- (* ifte false *) inversion_clear H' => //.
  by rewrite H1 in H.
  apply IHexec => //.
  rewrite /= negb_or in Hc.
  by case/andP : Hc.
- (* while true *) inversion_clear H' => //.
  + apply IHexec2 => //.
    have ->// : s' = s'0 by apply IHexec1.
  + by rewrite H in H2.
- (* while false *)
  inversion_clear H' => //.
  by rewrite H0 in H.
Qed.

Fixpoint cmd0_vars (c : cmd0) : list var.v :=
  match c with
    | skip => nil
    | x <- e => app_set (x :: nil) (vars_set e)
    | x <-* e => app_set (x :: nil) (vars_set e)
    | e1 *<- e2 => app_set (vars_set e1) (vars_set e2)
    | malloc x e => app_set (x :: nil) (vars_set e)
    | free e => vars_set e
  end.

Fixpoint cmd_vars (c : @while.cmd cmd0 expr_b) : list var.v :=
  match c with
    | while.cmd_cmd0 c0 => cmd0_vars c0
    | while.while b c' => app_set (vars_b_set b) (cmd_vars c')
    | c1 ; c2 => app_set (cmd_vars c1) (cmd_vars c2)
    | while.ifte b c1 c2 =>
      app_set (vars_b_set b) (app_set (cmd_vars c1) (cmd_vars c2))
  end.

Lemma In_cmd_vars : forall c x,
  x \in seplog_m.modified_vars c -> x \in cmd_vars c.
Proof.
elim=> //.
- case=> //.
  + move=> x e x' /=; rewrite mem_seq1 => /eqP ->{x'}.
    apply/inP/In_add_set_L => *; by apply/eqP.
  + move=> x e x' /=; rewrite mem_seq1 => /eqP ->{x'}.
    apply/inP/In_add_set_L => *; by apply/eqP.
  + move=> x e x' /=; rewrite mem_seq1 => /eqP ->{x'}.
    apply/inP/In_add_set_L => *; by apply/eqP.
- move=> c1 H1 c2 H2 x /=; rewrite mem_cat => /orP[/H1|/H2] /inP H.
  apply/inP/in_or_app_set; by left.
  apply/inP/in_or_app_set; by right.
- move=> b c1 H1 c2 H2 x /=; rewrite mem_cat => /orP[/H1|/H2] /inP H.
    apply/inP/in_or_app_set.
    right.
    apply/in_or_app_set; by auto.
  apply/inP/in_or_app_set.
  right.
  apply/in_or_app_set; by auto.
- move=> b e IH c /= /IH /inP H.
  apply/inP/in_or_app_set; by auto.
Qed.

(* TODO: changer les In x (seq_ext.s2l d) en x \in d *)
Lemma exec0_proj : forall c d s h s' h',
  Permutation d (cmd0_vars c) ->
  Some (s, h) -- c ----> Some (s', h') ->
  Some (store.proj s d, h) -- c ----> Some (store.proj s' d, h').
Proof.
case=> //.
- move=> d s h s' h' Hperm; inversion 1; subst; by constructor.
- move=> x e d s h d' h' Hperm; inversion 1; subst.
  rewrite /= in Hperm.
  have Hx : x \in d.
    apply/seq_ext.inP.
    eapply Permutation_in.
    exact/Permutation_sym/Hperm.
    exact: (seq_ext.In_add_set_L (vars_set e) x).
  rewrite store_proj_upd // -(eval_proj _ _ d).
  exact: exec0_assign.
  apply/seq_ext.incP.
  apply seq_ext.Permutation_incl_R with (seq_ext.add_set x (vars_set e)).
  by apply Permutation_sym; auto.
  eapply List.incl_tran; by [apply/seq_ext.incP/incl_vars_vars_set |apply seq_ext.incl_add_set].
- move=> x e d s h s' h' Hperm; inversion 1; subst.
  have Hx : x \in d.
    apply/seq_ext.inP.
    eapply Permutation_in.
    exact/Permutation_sym/Hperm.
    exact: (seq_ext.In_add_set_L (vars_set e) x).
  rewrite store_proj_upd //.
  apply exec0_lookup => //.
  rewrite eval_proj //.
  apply/seq_ext.incP.
  apply seq_ext.Permutation_incl_R with (seq_ext.add_set x (vars_set e)).
  by apply Permutation_sym; auto.
  eapply List.incl_tran; by [apply/seq_ext.incP/incl_vars_vars_set | apply seq_ext.incl_add_set].
- move=> e1 e2 d s h s' h' Hperm; inversion 1; subst.
  rewrite /= in Hperm.
  rewrite -(eval_proj e2 _ d); last first.
    eapply seq_ext.inc_trans.
    by apply/incl_vars_vars_set.
    apply seq_ext.inc_trans with (seq_ext.app_set (vars_set e1) (vars_set e2)).
    apply/seq_ext.incP/seq_ext.incl_app_set_R => *; by apply/eqP.
    apply/seq_ext.incP.
    eapply seq_ext.Permutation_incl_L; eauto.
    exact: List.incl_refl.
  apply exec0_mutation with v => //.
  rewrite (eval_proj e1 _ d) //; last first.
    eapply seq_ext.inc_trans.
    by apply/incl_vars_vars_set.
    apply seq_ext.inc_trans with (seq_ext.app_set (vars_set e1) (vars_set e2)).
    apply/seq_ext.incP/seq_ext.incl_app_set_L => *; by apply/eqP.
    apply/seq_ext.incP.
    eapply seq_ext.Permutation_incl_L; eauto.
    exact: List.incl_refl.
- move=> x e d s h s' h' Hperm; inversion 1; subst.
  rewrite /= in Hperm.
  have Hx : x \in d.
    apply/seq_ext.inP.
    eapply Permutation_in.
    exact/Permutation_sym/Hperm.
    exact: (seq_ext.In_add_set_L (vars_set e) x).
  rewrite store_proj_upd //.
  rewrite -(eval_proj _ _ d); last first.
    apply/seq_ext.incP.
    apply seq_ext.Permutation_incl_R with (seq_ext.add_set x (vars_set e)).
    by apply Permutation_sym; auto.
    eapply List.incl_tran; by [apply/seq_ext.incP/incl_vars_vars_set | apply seq_ext.incl_add_set].
  apply exec0_malloc.
  rewrite (eval_proj _ _ d) //; last first.
    apply/seq_ext.incP.
    apply seq_ext.Permutation_incl_R with (seq_ext.add_set x (vars_set e)).
    by apply Permutation_sym; auto.
    eapply List.incl_tran; by [apply/seq_ext.incP/incl_vars_vars_set | apply seq_ext.incl_add_set].
- move=> e d s h s' h' Hperm; inversion 1; subst.
  rewrite /= in Hperm.
  apply exec0_free with v => //.
  rewrite (eval_proj _ _ d) //; last first.
    apply/seq_ext.incP.
    apply seq_ext.Permutation_incl_R with (vars_set e).
    by apply Permutation_sym; auto.
    exact/incP/incl_vars_vars_set.
Qed.

(*Lemma exec_proj : forall c d s h s' h',
  Permutation (seq_ext.s2l d) (cmd_vars c) ->
  Some (s, h) -- c ---> Some (s', h') ->
  Some (store.store_heap.proj s d, h) -- c ---> Some (store.store_heap.proj s' d, h').
Proof.
elim=> //.
- move=> c d s h s' h' Hperm Hexec.
  constructor.
  apply exec0_proj => //.
  by inversion Hexec.
- move=> b c IH d s h s' h' Hperm.
  move HST : (Some (s, h)) => ST.
  move HST' : (Some (s', h')) => ST'.
  move HC : (while b c) => C.
  move=> Hexec.
  move: Hexec b c IH d s h s' h' Hperm HST HST' HC.
  elim=> //; clear ST ST' C.
  + move=> s h s' s'' b c Hb Hexec_c _ (* IH1 *) Hexec_while IH2 b_ c_ IH3 d s_ h_ s''_ h''_ Hperm.
    case=> X Y; subst s_ h_.
    destruct s'' => //.
    destruct s0 as [s'' h''].
    case=> X Y; subst s''_ h''_.
    case=> X Y; subst b_ c_.
    destruct s' as [[s' h']|].
    * apply exec_while_true with (Some (store.store_heap.proj s' d, h')) => //.
      rewrite eval_b_proj //.
      rewrite /= in Hperm.
      eapply incl_tran with (vars_b b).
      apply incl_vars_b_vars_b.
      eapply incl_tran with (seq_ext.app_set beq_nat (vars_b b) (cmd_vars c)).
      apply seq_ext.incl_app_set_L.
      apply beq_nat_eq.
      eapply seq_ext.Permutation_incl.
      apply Hperm.
      apply incl_refl.
      apply IH3.
      admit.
      done.
      apply IH2 with b c => //.
    * by move/from_none : Hexec_while.
  + move=> s h b c Hb b_ c_ IH d s_ h_ s__ h__ H [] X Y; subst s_ h_.
    case=> X Y; subst s__ h__.
    case=> X Y; subst b_ c_.
    apply exec_while_false.
    rewrite eval_b_proj //.
    admit.
+ admit.
+ admit.
(* TODO *)
Admitted.*)

End Syntax.

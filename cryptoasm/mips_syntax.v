(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import seq_ext.
Require Import machine_int.
Require Import mips_seplog mips_frame mips_tactics.
Import MachineInt.

Local Open Scope heap_scope.
Import mips_bipl.expr_m.
Local Open Scope mips_expr_scope.
Import mips_bipl.assert_m.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.

Lemma dom_heap_invariant0 s c s' : s -- c ----> s' ->
  forall st h st' h', s = Some (st, h) -> s' = Some (st', h') ->
    heap.dom h = heap.dom h'.
Proof.
case=> //; clear s c s'.
- (* nop *) move=> s st h st' h' -> [] _ <- //.
- (* add *) move=> st h rd rs rt Hcond st_ h_ st' h' [] _ <- [] _ <- //.
- (* addi *) move=> st h rd rs rt Hcond st_ h_ st' h' [] _ <- [] _ <- //.
- (* addiu *) move=> st h rt rs imm st_ h_ st' h' [] _ <- [] _ <- //.
- (* addu *) move=> st h rd rs rt st_ h_ st' h' [] _ <- [] _ <- //.
- (* cmd_and *) move=> st h rd rs rt st_ h_ st' h' [] _ <- [] _ <- //.
- (* andi *) move=> st h rt rs imm st_ h_ st' h' [] _ <- [] _ <- //.
- (* lw *) move=> st h rt off base p z Hp Hz st_ h_ st' h' [] _ <- [] _ <- //.
- (* lwxs *) move=> st h rt idx base p z Hp Hz st_ h_ st' h' [] _ <- [] _ <- //.
- (* maddu *) move=> st h rs rt st_ h_ st' h' [] _ <- [] _ <- //.
- (* mfhi *) move=> st h rd st_ h_ st' h' [] _ <- [] _ <- //.
- (* mflhxu *) move=> st h rd st_ h_ st' h' [] _ <- [] _ <- //.
- (* mflo *) move=> st h rd st_ h_ st' h' [] _ <- [] _ <- //.
- (* movn *) move=> st h rd rs rt Hcond st_ h_ st' h' [] _ <- [] _ <- //.
- move=> st h _ _ rt Hcond st_ h_ st' h' [] _ <- [] _ <- //.
- (* movz *) move=> st h rd rs rt Hcond st_ h_ st' h' [] _ <- [] _ <- //.
- move=> st h _ _ rt Hcond st_ h_ st' h' [] _ <- [] _ <- //.
- (* msubu *) move=> st h rs rt st_ h_ st' h' [] _ <- [] _ <- //.
- (* mthi *) move=> st h rs st_ h_ st' h' [] _ <- [] _ <- //.
- (* mtlo *) move=> st h rs st_ h_ st' h' [] _ <- [] _ <- //.
- (* multu *) move=> st h rs rt st_ h_ st' h' [] _ <- [] _ <- //.
- (* nor *) move=> st h rd rs rt st_ h_ st' h' [] _ <- [] _ <- //.
- (* cmd_or *) move=> st h rd rs rt st_ h_ st' h' [] _ <- [] _ <- //.
- (* sll *) move=> st h rx ry sa st_ h_ st' h' [] _ <- [] _ <- //.
- (* sllv *) move=> st h rd rt rs st_ h_ st' h' [] _ <- [] _ <- //.
- (* sltu *) move=> st h rd rt rs st_ h_ st' h' st'_ h'_ [] _ <- [] _ <- //.
- (* sra *) by move=> st h rd rt sa st_ h_ st' h' [] _ <- [] _ <-.
- (* srl *) by move=> st h rd rt sa st_ h_ st' h' [] _ <- [] _ <-.
- (* srlv *) by move=> st h rd rt rs st_ h_ st' h' [] _ <- [] _ <-.
- (* subu *) by move=> st h rd rs rt st_ h_ st' h' [] _ <- [] _ <-.
- (* sw *) move=> st h rt off base p Hp [z Hz] st_ h_ st'_ h'_ [] _ <- [] _ <-.
  by rewrite heap.dom_upd_invariant.
- (* xor *) by move=> st h rd rs rt st_ h_ st' h' [] _ <- [] _ <-.
- (* xori *) by move=> st h rt rs imm st_ h_ st' h' [] _ <- [] _ <-.
Qed.

Lemma dom_heap_invariant' s c s' : s -- c ---> s' ->
  forall st h st' h', s = Some (st, h) -> s' = Some (st', h') ->
    heap.dom h = heap.dom h'.
Proof.
elim=> //; clear s c s'.
- (* cmd0 *) move=> s c s' H st he st' he' Hs Hs'.
  by eapply dom_heap_invariant0; eauto.
- (* seq *) move=> s s' s'' c d Hc IHc Hd IHd /= st he st'' he'' Hs Hs''.
  destruct s' as [[st' he']|]; last first.
    move/semop_prop_m.from_none : Hd => Hd.
    by subst.
  eapply trans_eq.
  by eapply IHc; eauto.
  by eapply IHd; eauto.
- (* while true *) move=> [st h] s' s'' t c Ht Hc IH1 Hwhile IH2 st_ h_ st'' h'' [] _ <- Hs''.
  destruct s' as [[st' h']|].
  apply trans_eq with (heap.dom h').
  by apply (IH1 _ _ _ _ (refl_equal _) (refl_equal _)).
  eapply IH2; eauto.
  destruct s'' => //.
  by move/semop_prop_m.from_none : Hwhile.
- (* while false *)  by move=> [st h] t _ Ht st_ h_ st' h' [] _ <- [] _ <-.
Qed.

Lemma dom_heap_invariant s h c s' h' : Some (s, h) -- c ---> Some (s', h') ->
  heap.dom h = heap.dom h'.
Proof. intros. eapply dom_heap_invariant'; eauto. Qed.

Lemma reg_unchanged0 : forall (c : cmd0) st h st' h',
  Some (st, h) -- c ----> Some (st', h') ->
  forall x, x \notin (mips_frame.modified_regs c) ->
    [x]_st = [x]_st'.
Proof.
elim.
- move=> st h st' h'.
  case/exec0_nop_inv=> X Y; by subst.
- move=> rt rs imm st h st' h'.
  case/exec0_add_inv.
  + case=> H1 [] Hst' Hh'; subst => x /=.
    rewrite negb_and orbC /=.
    move/eqP => X.
    by rewrite store.get_upd.
  + by case.
- move=> rt rs imm st h st' h'.
  case/exec0_addi_inv.
  + case=> H1 [] Hst' Hh'; subst => x /=.
    rewrite negb_and orbC /=.
    move/eqP => X.
    by rewrite store.get_upd.
  + by case.
- move=> rt rs imm st h st' h'.
  case/exec0_addiu_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rd rs rt st h st' h'.
  case/exec0_addu_inv => Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rd rs rt st h st' h'.
  case/exec0_and_inv => Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rt rs imm st h st' h'.
  case/exec0_andi_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rt off base st h st' h'.
  case/exec0_lw_inv.
  move=> [p [Hp [z [Hz]]]] [] Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
  by case.
- (* lwxs *) move=> rt idx base st h st' h'.
  case/exec0_lwxs_inv.
  move=> [p [Hp [z [Hz]]]] [] Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
  by case.
- move=> rs rt st h st' h'.
  case/exec0_maddu_inv=> Hst' Hh'; subst => x /= _.
  by rewrite store.get_maddu_op.
- move=> rd st h st' h'.
  case/exec0_mfhi_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rd st h st' h'.
  case/exec0_mflhxu_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  rewrite store.get_mflhxu_op.
  by rewrite store.get_upd.
- (* mflo *) move=> rd st h st' h'.
  case/exec0_mflo_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- (* movn *) move=> rd rs rt st h st' h'.
  case/exec0_movn_inv.
  move=> [Hrt []] Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
  move=> [Hrt []] Hst' Hh'; by subst.
- move=> rd rs rt st h st' h'.
  case/exec0_movz_inv.
  move=> [Hrt []] Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
  move=> [Hrt []] Hst' Hh'; by subst.
- move=> rs rt st h st' h'.
  case/exec0_msubu_inv=> Hst' Hh'; subst => x _.
  by rewrite store.get_msubu_op.
- move=> rs st h st' h'.
  case/exec0_mthi_inv=> Hst' Hh'; subst => x _.
  by rewrite store.get_mthi_op.
- (* mtlo *) move=> rs st h st' h'.
  case/exec0_mtlo_inv=> Hst' Hh'; subst => x _.
  by rewrite store.get_mtlo_op.
- move=> rs rt st h st' h'.
  case/exec0_multu_inv=> Hst' Hh'; subst => x _.
  by rewrite store.get_multu_op.
- move=> rd rs rt st h st' h'.
  case/exec0_nor_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rd rs rt st h st' h'.
  case/exec0_or_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- (* sll *) move=> rx ry sa st h st' h'.
  case/exec0_sll_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rd rt rs st h st' h'.
  case/exec0_sllv_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rd rt rs st h st' h'.
  case/exec0_sltu_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- (* sra *) move=> rd rt sa st h st' h'.
  case/exec0_sra_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- (* srl *) move=> rd rt sa st h st' h'.
  case/exec0_srl_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rd rt rs st h st' h'.
  case/exec0_srlv_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rd rt rs st h st' h'.
  case/exec0_subu_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rt off base st h st' h'.
  case/exec0_sw_inv.
  move=> [p [Hp [z [Hz]]]] [] Hst' Hh'; by subst.
  by case.
- (* xor *) move=> rd rs rt st h st' h'.
  case/exec0_xor_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
- move=> rt rs imm st h st' h'.
  case/exec0_xori_inv=> Hst' Hh'; subst => x /=.
  rewrite negb_and orbC /=.
  move/eqP => X.
  by rewrite store.get_upd.
Qed.

Lemma reg_unchanged' s c s' : (s -- c ---> s') ->
  forall x st h st' h', ~ List.In x (modified_regs c) ->
    s = Some (st, h) -> s' = Some (st', h') ->
    store.get x st = store.get x st'.
Proof.
elim => //; clear s c s'.
- (* cmd0 *) move=> s c s' H x st h st' h' Hx Hs Hs'.
  subst.
  eapply reg_unchanged0.
  apply H.
  apply/negP.
  by move/inP.
- (* seq *) move=> s s' s'' c d Hc IHc Hd IHd x st h st'' h'' Hx Hs Hs''.
  destruct s' as [[st' h']|]; last first.
    move/semop_prop_m.from_none : Hd => Hd; by subst.
  eapply trans_eq.
  eapply IHc.
  contradict Hx.
  rewrite /=.
  apply List.in_or_app; by left.
  apply Hs.
  reflexivity.
  eapply IHd.
  contradict Hx.
  rewrite /=.
  apply List.in_or_app; by right.
  reflexivity.
  by apply Hs''.
- (* if true *) move=> [s h] s' t c d Ht Hc IH x st he st' he' Hx [] X Y Hs'; subst.
  eapply IH.
  contradict Hx.
  rewrite /=.
  apply List.in_or_app; by left.
  reflexivity.
  reflexivity.
- (* if false *) move=> [s h] s' t c d Ht Hc IH x st he st' he' Hx [] X Y Hs'; subst.
  eapply IH.
  contradict Hx.
  rewrite /=.
  apply List.in_or_app; by right.
  reflexivity.
  reflexivity.
- (* while true *) move=> [s h] s' s'' t c Ht Hc IHc Hwhile IHwhile x st he st'' he'' Hx [] X Y Hs''; subst.
  destruct s' as [[st' he']|]; last first.
    move/semop_prop_m.from_none : Hwhile => Hwhile; by subst.
  eapply trans_eq.
  eapply IHc.
  done.
  reflexivity.
  reflexivity.
  eapply IHwhile.
  done.
  reflexivity.
  reflexivity.
- (* while false *) move=> [s h] t c Ht x st he st' he' Hx [] X Y [] U V; subst.
  by subst.
Qed.

Lemma reg_unchanged : forall st h c st' h',
  Some (st, h) -- c ---> Some (st', h') ->
  forall x, ~ List.In x (modified_regs c) ->
    store.get x st = store.get x st'.
Proof. intros. eapply reg_unchanged'; eauto. Qed.

Ltac Reg_unchanged :=
  match goal with
    | Hid : (Some (?st1, ?h1) -- ?c ---> Some (?st2, ?h2))%mips_cmd 
     |- ( [ ?r1 ]_ ?st1 = [ ?r2 ]_ ?st2 )%mips_expr =>
        apply reg_unchanged with h1 c h2; [exact Hid | idtac]
    | Hid : WMIPS_Semop.exec (Some (?st1, ?h1)) ?c (Some (?st2, ?h2))
      |- ( [ ?r1 ]_ ?st1 = [ ?r2 ]_ ?st2 )%mips_expr =>
        apply reg_unchanged with h1 c h2; [exact Hid | idtac]
  end.

Lemma triple_exec_proj0 (P : assert) c (Q : assert) :
  (mips_seplog.hoare0 P c Q) ->
    forall st h st' h' d,
      P st (heap.proj h d) ->
      (Some (st, h) -- c ----> Some (st', h')) ->
      (Some (st, heap.proj h d) -- c ----> Some (st', heap.proj h' d)).
Proof.
elim=> //; clear P c Q.
- move=> P st h st' h' d _.
  case/exec0_nop_inv => -> ->; by constructor.
- move=> Q rs rt rd st h st' h' d _.
  case/exec0_add_inv.
  + case=> Hcond [] -> ->; by constructor.
  + by case.
- move=> Q rt rs imm st h st' h' d _.
  case/exec0_addi_inv.
  + case=> Hcond [] -> ->; by constructor.
  + by case.
- move=> Q rt rs imm st h st' h' d _.
  case/exec0_addiu_inv=> -> ->; by constructor.
- move=> Q rs rt rd st h st' h' d _.
  case/exec0_addu_inv=> -> ->; by constructor.
- move=> Q rd rs rt st h st' h' d _.
  case/exec0_and_inv => -> ->; by constructor.
- move=> Q rt rs imm st h st' h' d _.
  case/exec0_andi_inv => -> ->; by constructor.
- move=> Q rt off base st h st' h' d Hpre.
  case/exec0_lw_inv.
  + case=> p [] Hp [] z [] Hz [] -> ->.
    apply exec0_lw with p => //.
    rewrite heap.get_proj //.
    rewrite /mips_seplog.wp_lw in Hpre.
    case: Hpre => p' [] Hp' [] z' [] Hz' HQ.
    have ? : p = p' by rewrite [u2Z _]/= in Hp'; lia.
    subst p'.
    apply/seq_ext.inP.
    move/heap.get_Some_in_dom : Hz'; move/seq_ext.inP.
    move: (heap.inc_dom_proj d h).
    move/seq_ext.incP.
    by apply.
  + by case.
- move=> rt idx base Q st h st' h' d Hpre.
  case/exec0_lwxs_inv.
  + case=> p [] Hp [] z [] Hz [] -> ->.
    apply exec0_lwxs with p => //.
    rewrite heap.get_proj //.
    rewrite /mips_seplog.wp_lwxs in Hpre.
    case: Hpre => p' [] Hp' [] z' [] Hz' HQ.
    have ? : p = p' by rewrite [u2Z _]/= in Hp'; lia.
    subst p'.
    apply/seq_ext.inP.
    move/heap.get_Some_in_dom : Hz'; move/seq_ext.inP.
    move: (heap.inc_dom_proj d h).
    move/seq_ext.incP.
    by apply.
  + by case.
- move=> Q rs rt st h st' h' d _.
  case/exec0_maddu_inv=> -> ->; by constructor.
- move=> Q rd st h st' h' d _.
  case/exec0_mfhi_inv=> -> ->; by constructor.
- move=> rd Q st h st' h' d _.
  case/exec0_mflhxu_inv=> -> ->; by constructor.
- move=> Q rd st h st' h' d _.
  case/exec0_mflo_inv=> -> ->; by constructor.
- move=> Q rd rs rt st h st' h' d _.
  case/exec0_movn_inv.
  + case=> Htest [] -> ->; by apply exec0_movn_true.
  + case=> Htest [] -> ->; by apply exec0_movn_false.
- move=> Q rd rs rt st h st' h' d _.
  case/exec0_movz_inv.
  + case=> Htest [] -> ->; by apply exec0_movz_true.
  + case=> Htest [] -> ->; by apply exec0_movz_false.
- move=> Q rs rt st h st' h' d _.
  case/exec0_msubu_inv=> -> ->; by constructor.
- move=> Q rs st h st' h' d _.
  case/exec0_mthi_inv=> -> ->; by constructor.
- move=> Q rs st h st' h' d _.
  case/exec0_mtlo_inv => -> ->; by constructor.
- move=> Q rs rt st h st' h' d _.
  case/exec0_multu_inv=> -> ->; by constructor.
- move=> Q rd rs rt st h st' h' d _.
  case/exec0_nor_inv=> -> ->; by constructor.
- move=> Q rd rs rt st h st' h' d _.
  case/exec0_or_inv=> -> ->; by constructor.
- move=> Q rx ry sa st h st' h' d _.
  case/exec0_sll_inv=> -> ->; by constructor.
- move=> Q rd rs rt st h st' h' d _.
  case/exec0_sllv_inv=> -> ->; by constructor.
- move=> Q rd rs rt st h st' h' d _.
  case/exec0_sltu_inv=> -> ->; by constructor.
- (* sra *) move=> Q rd rt sa st h st' h' d _.
  case/exec0_sra_inv=> -> ->; by constructor.
- move=> Q rd rt sa st h st' h' d _.
  case/exec0_srl_inv=> -> ->; by constructor.
- move=> Q rd rt rs st h st' h' d _.
  case/exec0_srlv_inv=> -> ->; by constructor.
- move=> Q rs rt rd st h st' h' d _.
  case/exec0_subu_inv=> -> ->; by constructor.
- move=> rt off base Q st h st' h' d Hpre.
  case/exec0_sw_inv.
  + case=> p [] Hp [] z [] Hz [] -> ->.
    rewrite heap.proj_upd.
    apply exec0_sw => //.
    exists z.
    rewrite heap.get_proj //.
    rewrite /mips_seplog.wp_sw in Hpre.
    case: Hpre => p' [] Hp' [] [] z' Hz' HQ.
    have ? : p = p' by rewrite [u2Z _]/= in Hp'; lia.
    subst p'.
    apply/seq_ext.inP.
    move/heap.get_Some_in_dom : Hz'; move/seq_ext.inP.
    move: (heap.inc_dom_proj d h).
    move/seq_ext.incP.
    by apply.
  + by case.
- move=> Q rd rs rt st h st' h' d Hpre.
  case/exec0_xor_inv=> -> ->; by constructor.
- move=> Q rt rs imm st h st' h' d Hpre.
  case/exec0_xori_inv=> -> ->; by constructor.
Qed.

Lemma triple_exec_proj P c Q :
  mips_seplog.WMIPS_Hoare.hoare P c Q ->
  forall d st h st' h',
    P st (heap.proj h d) ->
    Some (st, h) -- c ---> Some (st', h') ->
    Some (st, heap.proj h d) -- c ---> Some (st', heap.proj h' d).
Proof.
elim=> //; clear P c Q.
- move=> P Q c Htriple d st h st' h' HP Hc.
  apply while.exec_cmd0.
  eapply triple_exec_proj0; eauto.
  by inversion Hc.
- move=> P Q R c1 c2 Hc1 IHc1 Hc2 IHc2 d st h st' h' HP.
  case/semop_prop_m.exec_seq_inv.
  case.
  + case=> st'' h'' [] Hc1' Hc2'.
    apply while.exec_seq with (Some (st'', heap.proj h'' d)).
    apply IHc1 => //.
    apply IHc2 => //.
    move/hoare_prop_m.soundness : Hc1 => Hc1.
    rewrite /hoare_semantics in Hc1.
    move/Hc1 : (HP) => HP'.
    case: HP' => _ HP'.
    apply HP' => //.
    by apply IHc1.
  + case=> _.
    by move/semop_prop_m.from_none.
- move=> P P' Q Q' c HQ'Q HPP' Hc IHc s st h st' h' HP Hexec_c.
  apply IHc; last by [].
  by apply HPP'.
- move=> P t c Htriple_c IHc d st h st' h' HP.
  move Hs : (Some (st, h)) => s.
  move Hs' : (Some (st', h')) => s'.
  move Hwhile : (while.while t c) => C.
  move=> Hexec_C.
  move: Hexec_C P t c Htriple_c IHc d st h st' h' HP Hs' Hs Hwhile.
  elim=> //; clear s s' C.
  + move=> [s h] s' s'' t c Ht H_exec_c IH_exec_c H_exec_while IH_exec_while P t_ c_ Hhoare_c_ IH d s_ h_ st'' h'' HP.
    destruct s' as [[s' h']|].
    * move=> Hs'' [] X Y.
      subst s_ h_.
      case=> X Y; subst t_ c_.
      case/boolP : (eval_b t s) => X.
      - apply while.exec_while_true with (Some (s', heap.proj h' d)) => //.
        by apply IH.
        apply: (IH_exec_while _ _ _ Hhoare_c_) => //.
        move/hoare_prop_m.soundness in Hhoare_c_.
        rewrite /hoare_semantics in Hhoare_c_.
        apply: (proj2 (Hhoare_c_ _ _ (conj HP X))).
        by apply IH.
      - by rewrite Ht in X.
    * move/semop_prop_m.from_none : H_exec_while.
      by move=> ->.
  + move=> [s h] t c Ht P t_ c_ Hhoare_c IH d st_ h_ st' h' HP.
    case=> X Y; subst.
    case=> X Y; subst.
    case=> X Y; subst.
    by apply while.exec_while_false.
- move=> P Q t c1 c2.
  move=> Hhoare_c1 IHc1 Hhoare_c2 IHc2 d st h st' h' HP.
  case/boolP : (eval_b t st) => X.
  + move/(semop_prop_m.exec_ifte_true_inv _ _ _ _ _ _ X) => Hc1.
    apply while.exec_ifte_true => //; by apply IHc1.
  + move/(semop_prop_m.exec_ifte_false_inv _ _ _ _ _ _ X) => Hc2.
    apply while.exec_ifte_false => //; by apply IHc2.
Qed.

Lemma exec_deter_proj0 s (c : cmd0) s' : s -- c ----> s'  ->
  forall st h st' h' d st'_proj h'_proj,
    s = Some (st, h) -> s' = Some (st',h') ->
    Some (st, heap.proj h d) -- c ----> Some (st'_proj, h'_proj) ->
    st'_proj = st' /\ h'_proj = heap.proj h' d /\ h \D\ d = h' \D\ d.
Proof.
case=> //; clear s c s'.
- move=> s st h st' h' d st'_proj h'_proj [] -> [] X Y.
  subst st' h'; by case/exec0_nop_inv.
- move=> st h rd rs rt Hcond st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'.
  case/exec0_add_inv.
  + by case=> _ [].
  + tauto.
- move=> st h rt rs imm Hcond st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'.
  case/exec0_addi_inv.
  + by case=> _ [].
  + tauto.
- move=> st h rt rs imm st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'; by case/exec0_addiu_inv.
- move=> st h rt rs imm st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'; by case/exec0_addu_inv.
- move=> st h rd rs rt st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'; by case/exec0_and_inv.
- move=> st h rt rs imm st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'; by case/exec0_andi_inv.
- move=> st h rt off base p z Hp Hz st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'.
  case/exec0_lw_inv.
  + case=> p_ [Hp_ [z_ [Hz_ []] ]] Heq.
    split=> //.
    have {Hp_}X : p = p_ by lia. subst p_.
    move/heap.get_Some_in_dom : (Hz_); move/seq_ext.inP.
    move/seq_ext.incP : (heap.inc_dom_proj d h) => X; move/X => p_d.
    rewrite heap.get_proj // in Hz_; last by apply/seq_ext.inP.
    rewrite Heq.
    f_equal.
    rewrite Hz in Hz_.
    by case: Hz_.
  + by case.
- move=> st h rt ids base p z Hp Hz st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'.
  case/exec0_lwxs_inv.
  + case=> p_ [] Hp_ [] z_ [] Hz_ [] -> ->.
    split=> //.
    have Hpp_ : p = p_ by lia.
    subst p_.
    move/heap.get_Some_in_dom : (Hz_); move/seq_ext.inP.
    move/seq_ext.incP : (heap.inc_dom_proj d h) => X; move/X => Hp_in_d.
    rewrite heap.get_proj // in Hz_; last by apply/seq_ext.inP.
    rewrite Hz in Hz_; by case : Hz_ => ->.
  + by case.
- move=> st h rs rt st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_maddu_inv=> -> ->.
- move=> st h rd st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_mfhi_inv=> -> ->.
- move=> st h rd st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_mflhxu_inv=> -> ->.
- move=> st h rd st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_mflo_inv=> -> ->.
- move=> st h rd rs rt Hcond st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  case/exec0_movn_inv.
  + by case=> Hcond' [] -> ->.
  + case; tauto.
- move=> st h rd rs rt Hcond st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  case/exec0_movn_inv.
  + case; tauto.
  + by case=> Hcond' [] -> ->.
- move=> st h rd rs rt Hcond st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  case/exec0_movz_inv.
  + by case=> Hcond' [] -> ->.
  + case; tauto.
- move=> st h rd rs rt Hcond st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  case/exec0_movz_inv.
  + case; tauto.
  + by case=> Hcond' [] -> ->.
- move=> st h rs rt st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_msubu_inv=> -> ->.
- move=> st h rs st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_mthi_inv=> -> ->.
- move=> st h rs st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_mtlo_inv=> -> ->.
- move=> st h rs rt st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_multu_inv=> -> ->.
- move=> st h rd rs rt st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_nor_inv=> -> ->.
- move=> st h rd rs rt st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_or_inv=> -> ->.
- move=> st h rx ry sa st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_sll_inv=> -> ->.
- move=> st h rd rt rs st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_sllv_inv=> -> ->.
- move=> st h rd rs rt st_ h_ st' h' st'_ h'_ d st'_proj h'_proj [] <- <- [] <- <-.
  case/exec0_sltu_inv=> -> ->.
  by rewrite -h_.
- (* sra *) move=> st h rd rt sa st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_sra_inv=> -> ->.
- (* srl *) move=> st h rd rt sa st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_srl_inv=> -> ->.
- move=> st h rd rt rs st_ h_ st' h' d st'_proj h'_proj [] <- <- [] <- <-.
  by case/exec0_srlv_inv=> -> ->.
- move=> st h rt rs imm st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'.
  by case/exec0_subu_inv.
- (* sw *) move=> st h rt off base p HP [z Hz] st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'.
  case/exec0_sw_inv.
  (* no error *)
  + case=> p_ [Hp_ [z_ [Hz_ []]]] Heq.
    have {Hp_}X : p = p_ by lia. subst p_.
    move/heap.get_Some_in_dom : (Hz_); move/seq_ext.inP.
    move/seq_ext.incP : (heap.inc_dom_proj d h) => X; move/X => Hp_in_d.
    rewrite heap.get_proj // in Hz_; last by apply/seq_ext.inP.
    rewrite Hz in Hz_. case: Hz_ => ?; subst z_.
    split; first by [].
    split.
    * by rewrite heap.proj_upd.
    * rewrite heap.difs_upd //; by apply/seq_ext.inP.
  + by case.
- (* xor *) move=> st h rd rs rt st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'; by case/exec0_xor_inv.
- (* xori *) move=> st h rt rs imm st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  case=> X Y; subst st' h'; by case/exec0_xori_inv.
Qed.

Lemma exec_deter_proj' s c s' : s -- c ---> s' ->
  forall st h st' h' d st'_proj h'_proj,
    s = Some (st, h) -> s' = Some (st', h') ->
    Some (st, heap.proj h d) -- c ---> Some (st'_proj, h'_proj) ->
    st' = st'_proj /\ h'_proj = heap.proj h' d /\ h \D\ d = h' \D\ d.
Proof.
elim=> //; clear s c s'.
- (* cmd0 *) move=> s c s' H st h st' h' d st'_proj h'_proj Hs Hs' Hc.
  inversion Hc; subst.
  move: (exec_deter_proj0 _ _ _ H st h st' h' d _ _ (refl_equal _) (refl_equal _) H2).
  by case => H1 [h2 H3].
- (* seq *) move=> s s'' s' c1 c2 Hc1 IHc1 Hc2 IHc2 st h st' h' d st'_proj h'_proj Hs Hs'.
  subst s s'.
  case/semop_prop_m.exec_seq_inv.
  case.
  + case=> st''_proj h''_proj [Hc1' Hc2'].
    destruct s'' as [[st''_ h'']|].
    - case : {IHc1}(IHc1 st h st''_ h'' d st''_proj h''_proj (refl_equal _) (refl_equal _) Hc1') => IHc1 [IHc1' IHc1''].
      subst st''_ h''_proj.
      case : {IHc2}(IHc2 st''_proj h'' st' h' d _ _ (refl_equal _) (refl_equal _) Hc2') => IHc2 [IHc2' IHc2''].
      subst st'_proj h'_proj.
      by rewrite IHc1'' IHc2''.
    - by move/semop_prop_m.from_none : Hc2.
  + case=> H1; by move/semop_prop_m.from_none.
- (* if true *) move=> [st h] s' t c1 c2 Ht Hc IHc st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  move=> Hs'.
  move=> H.
  apply semop_prop_m.exec_ifte_true_inv in H; last by [].
  by apply (IHc st h st' h' d _ _ (refl_equal _) Hs' H).
- (* if false *) move=> [st h] s' t c1 c2 Ht Hc IHc st_ h_ st' h' d st'_proj h'_proj [] X Y; subst st_ h_.
  move=> Hs'.
  move=> H.
  apply semop_prop_m.exec_ifte_false_inv in H; last by [].
  by apply (IHc st h st' h' d _ _ (refl_equal _) Hs' H).
- (* while true *) move=> [st h] s'' s' t c Ht Hc IHc Hwhile IHwhile st_ h_ st' h' d st'_proj h'_proj [] X Y.
  subst st_ h_ => Hs' H.
  apply semop_prop_m.exec_while_inv_true in H; last by [].
  case : H => st''_proj [h''_proj [Hc' Hwhile']].
  destruct s'' as [[st''_ h''_]|].
  + move: {IHc}(IHc st h st''_ h''_ d st''_proj h''_proj (refl_equal _) (refl_equal _) Hc') => [IHc1 [IHc2 IHc3]].
    subst st''_ h''_proj.
    move: {IHwhile}(IHwhile st''_proj h''_ st' h' d _ _ (refl_equal _) Hs' Hwhile') => IHwhile.
    split; first by tauto.
    split; first by tauto.
    rewrite IHc3; tauto.
  + move/semop_prop_m.from_none in Hwhile; by subst.
- (* while false *) move=> [st h] t c Ht st_ h_ st__ h__ d st'_proj h'_proj [] X Y.
  subst st_ h_. move=> [] X Y.
  subst st__ h__.
  by case/semop_prop_m.exec_while_inv_false.
Qed.

Lemma exec_deter_proj : forall st h c st' h', Some (st, h) -- c ---> Some (st', h') ->
  forall d st'_proj h'_proj,
    Some (st, heap.proj h d) -- c ---> Some (st'_proj, h'_proj) ->
    st' = st'_proj /\ h'_proj = heap.proj h' d /\ h \D\ d = h' \D\ d.
Proof.
intros.
eapply exec_deter_proj'.
by apply H.
reflexivity.
reflexivity.
by apply H0.
Qed.

Definition is_sw (c : cmd0) : bool :=
  match c with | sw _ _ _ => true | _ => false end.

(* TODO: inelegant *)
Fixpoint contains_sw (c : @while.cmd cmd0 expr_b) : bool :=
  match c with
    | while.cmd_cmd0 c0 => is_sw c0
    | c ; d => contains_sw c || contains_sw d
    | while.ifte _ c d => contains_sw c || contains_sw d
    | while.while _ c => contains_sw c
  end.

Lemma no_sw_heap_invariant_cmd0 s (c : cmd0) s' :
  (s -- c ----> s') ->
  ~~ contains_sw c ->
  forall st h st' h',
    s = Some (st, h) -> s' = Some (st', h') ->
    h = h'.
Proof.
elim=> //; clear s c s'.
- (* nop *) move=> s _ st he st' he' -> [] //.
- (* add *) move=> s ha rd rs rt H _ st he st' he' [] X Y [] U V; by subst.
- (* addi *) move=> s h rt rs imm H _ st he st' he' [] X Y [] U V; by subst.
- (* addiu *) move=> s h rt rs imm _ st he st' he' [] X Y [] U V; by subst.
- (* addu *) move=> s h rd rs rt _ st he st' he' [] X Y [] U V; by subst.
- (* cmd_and *) move=> s h rd rs rt _ st he st' he' [] X Y [] U V; by subst.
- (* andi *) move=> s h rd rs rt _ st he st' he' [] X Y [] U V; by subst.
- (* lw *) move=> s h rt off base p z Hp Hz _ st he st' he' [] X Y [] U V; by subst.
- (* lwxs *) move=> s h rt idx base p z Hp Hz _ st he st' he' [] X Y [] U V; by subst.
- (* maddu *) move=> s h rs rt _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* mfhi *) move=> s h rd _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* mflhxu *) move=> s h rd _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* mflo *) move=> s h rd _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* movn *) move=> s h rd rs rt H _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* movn *) move=> s h rd rs rt H _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* movz *) move=> s h rd rs rt H _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* movz *) move=> s h rd rs rt H _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* msubu *) move=> s h rs rt _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* mthi *) move=> s h rs _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* mtlo *) move=> s h rs _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* multu *) move=> s h rs rt _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* nor *) move=> s h rd rs rt _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* or *) move=> s h rd rs rt _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* sll *) move=> s h rx ry sa _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* sllv *) move=> s h rd rt rs _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* sltu *) move=> s h rd rs rt flag H _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* sra *) by move=> s h rd rt sa _ s_ h_ st' h' [] _ <- [] _ <-.
- (* srl *) by move=> s h rd rt sa _ s_ h_ st' h' [] _ <- [] _ <-.
- (* srlv *) move=> s h rd rt rs _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* subu *) move=> s h rd rs rt _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* xor *) move=> s h rd rs rt _ s_ h_ st' h' [] _ <- [] _ <- //.
- (* xori *) move=> s h rt rs imm _ s_ h_ st' h' [] _ <- [] _ <- //.
Qed.

Lemma no_sw_heap_invariant s c s' :
  s -- c ---> s' -> ~~ contains_sw c ->
  forall st h st' h', s = Some (st, h) -> s' = Some (st', h') ->
    h = h'.
Proof.
elim=> //; clear s c s'.
- (* cmd0 *) move=> s c s' H Hcontains st he st' he' Hs Hs'.
  eapply no_sw_heap_invariant_cmd0.
  apply H.
  done.
  apply Hs.
  apply Hs'.
- (* seq *) move=> s s' s'' c d Hc IHc Hd IHd /= Hcontains st he st'' he'' Hs Hs''.
  destruct s' as [[st' he']|]; last first.
    move/semop_prop_m.from_none : Hd => Hd.
    by subst.
  eapply trans_eq.
  eapply IHc.
  apply/negP. move/orP : Hcontains. tauto.
  apply Hs.
  reflexivity.
  eapply IHd.
  apply/negP. move/orP : Hcontains. tauto.
  reflexivity.
  apply Hs''.
- (* ifte true *) move=> [st h] s' t c1 c2 Ht Hc1 IHc1 Hcontains st_ h_ st' h' [] X Y.
  subst st_ h_ => Hs'.
  apply IHc1 with st st' => //.
  move: Hcontains.
  rewrite /= negb_or.
  by case/andP.
- (* ifte false *) move=> [st h] s' t c1 c2 Ht Hc2 IHc2 Hcontains st_ h_ st' h' [] X Y.
  subst st_ h_ => Hs'.
  apply IHc2 with st st' => //.
  move: Hcontains.
  rewrite /= negb_or.
  by case/andP.
- (* while true *) move=> [s h] s' s'' b c Hb Hc IHc Hwhile IHwhile Hcontains s_ h_ st'' h'' [] _ <- Hs''.
  destruct s' as [[st' h']|].
  eapply trans_eq.
  eapply IHc => //.
  eapply IHwhile => //.
  apply Hs''.
  subst s''.
  by move/semop_prop_m.from_none : Hwhile.
- (* while false *) move=> [s h] b c Hb Hcontains s_ h_ s__ h__.
  case=> _ <-.
  by case=> _ <-.
Qed.

Lemma safety_monotonicity0 (s : option state) (c : cmd0) (s' : option state) :
   (s -- c ----> s') ->
   forall (st : store.t) (h0 : heap.t) (st' : store.t)
     (h' : heap.t),
   Some (st, h0) = s ->
   Some (st', h') = s' ->
   forall h'' : heap.t,
   heap.disj h0 h'' ->
   (Some (st, heap.union h0 h'') -- c ----> Some (st', heap.union h' h'')) /\
   heap.disj h' h''.
Proof.
elim=> //; clear s c s'.
- (* skip *) move=> st st0 h st' h' [] X [] Y h'' Hdisj.
  subst st.
  case: Y => Y Z; subst.
  split; [by constructor | assumption].
- (* add *) move=> st h rd rs rt Hcond st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* addi *) move=> st h rt rs imm Hcond st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* addiu *) move=> st h rt rs imm st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* addu *) move=> st h rd rs rt st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* cmd_and *) move=> st h rd rs rt st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* andi *) move=> st h rt rs imm st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* lw *) move=> s h rt off base p z Hp Hz st he st' he' [] X Y [] Z U; subst.
  move=> h'' Hdisj.
  split=> //.
  econstructor; eauto.
  by apply heap.get_union_L.
- (* lwxs *) move=> s h rt idx base p z Hp Hz st he st' he' [] X Y [] Z U; subst.
  move=> h'' Hdisj.
  split=> //.
  econstructor; eauto.
  by apply heap.get_union_L.
- (* maddu *) move=> st h rs rt st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* mfhi *) move=> st h rd st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* mflhxu *) move=> st h rd st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* mflo *) move=> st h rd st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* movn true *) move=> st h rd rs rt Hcond st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* movn false *) move=> st h rd rs rt Hcond st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* movz true *) move=> st h rd rs rt Hcond st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* movz false *) move=> st h rd rs rt Hcond st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* msubu *) move=> st h rs rt st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* mthi *) move=> st h rd st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* mtlo *) move=> st h rd st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* multu *) move=> st h rs rt st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* nor *) move=> st h rd rs rt st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* cmd_or *) move=> st h rd rs rt st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* sll *) move=> st h rx ry sa st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* sllv *) move=> st h rd rs rt st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* sltu *) move=> st h rd rs rt flag Hflas st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* sra *) move=> st h rd rt sa st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* srl *) move=> st h rd rt sa st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* srlv *) move=> st h rd rt sa st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* subu *) move=> st h rd rs rt st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* sw *) move=> s h rt off base p Hp [z Hz] st he st' he' [] X Y [] Z U; subst.
  move=> h'' Hdisj.
  rewrite -(heap.upd_union_L _ _ _ _ _ z) //.
  split.
  + econstructor; eauto.
    exists z.
    by apply heap.get_union_L.
  + by apply heap.disj_upd.
- (* xor *) move=> st h rd rs rt st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
- (* xori *) move=> st h rt rs imm st_ h_ st' h' [] -> -> [] -> -> h'' Hdisj.
  split; [by constructor | assumption].
Qed.

Lemma safety_monotonicity c st h st' h' :
    (Some (st, h) -- c ---> Some (st', h')) ->
    forall h'',
      heap.disj h h'' ->
      (Some (st, heap.union h h'') -- c ---> Some (st', heap.union h' h'')) /\
      heap.disj h' h''.
Proof.
move Hs : (Some (st, h)) => s.
move Hs' : (Some (st', h')) => s'.
move=> Hexec.
move: Hexec st h st' h' Hs Hs'.
elim=> //; clear c s s'.
- move=> s c s' H st h0 st' h' X Y h'' Hdisj.
  case: (safety_monotonicity0 _ _ _ H _ _ _ _ X Y h'' Hdisj) => H1 H2.
  split => //.
  by constructor.
- move=> s s' s'' c1 c2 Hc1 IHc1 Hc2 IHc2 st h st'' h'' Hs Hs' h_disj Hdisj.
  destruct s' as [[st' h']|].
  - case: (IHc1 _ _ _ _ Hs (refl_equal _) _ Hdisj) => H1 H2.
    case: (IHc2 _ _ _ _ (refl_equal _) Hs' _ H2) => H3 H4.
    split => //.
    apply while.exec_seq with (Some (st', heap.union h' h_disj)) => //.
  - destruct s'' as [[st''_ h''_]|] => //.
    by move/semop_prop_m.from_none : Hc2.
- move=> [st h] s' b c1 c2 Hb Hc1 IHc1 st_ h_ st' h' [] -> -> Hs' h'' Hh''.
  case: {IHc1}(IHc1 _ _ _ _ (refl_equal _) Hs' _ Hh'').
  split=> //.
  by apply while.exec_ifte_true.
- move=> [st h] s' b c1 c2 Hb Hc1 IHc1 st_ h_ st' h' [] -> -> Hs' h'' Hh''.
  case: {IHc1}(IHc1 _ _ _ _ (refl_equal _) Hs' _ Hh'').
  split=> //.
  by apply while.exec_ifte_false.
- move=> [st h] s' s'' b c Hb Hc IHc Hwhile IHwhile st_ h_ st'' h'' [] -> -> Hs'' h2 Hh2.
  destruct s' as [[st' h']|].
  + case: (IHc _ _ _ _ (refl_equal _) (refl_equal _) _ Hh2) => Htmp Htmp'.
    subst s''.
     case: (IHwhile _ _ _ _ (refl_equal _) (refl_equal _) _ Htmp') => Htmp'' Htmp'''.
     split=> //.
     by apply while.exec_while_true with (Some (st', heap.union h' h2)).
  + subst s''.
    by move/semop_prop_m.from_none : Hwhile.
- move=> [st h] b c Hb st_ h_ st' h' [] -> -> [] -> -> h2 Hh2.
  split=> //.
  by apply while.exec_while_false.
Qed.

From mathcomp Require Import seq.

Lemma exec_termi_proj0 (s : option state) (c : cmd0) (s' : option state) :
   s -- c ----> s' ->
   forall (st : store.t) (h0 : heap.t) d,
   Some (st, h0) = s ->
   exists s'_ : option state, Some (st, heap.proj h0 d) -- c ---> s'_.
Proof.
case=> //; clear s c s'.
- move=> s st h d [] Hs.
  eapply ex_intro.
  constructor.
  by apply exec0_nop.
- move=> st h rd rs rt Hcond st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_add.
- move=> st h rd rs rt Hcond st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_add_error.
- move=> st h rt rs imm Hcond st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_addi.
- move=> st h rt rs imm Hcond st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_addi_error.
- move=> st h rt rs imm st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_addiu.
- move=> st h rd rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_addu.
- move=> st h rd rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_and.
- move=> st h rt rs imm st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_andi.
- move=> st h rt off base p z Hp Hz st_ h_ d [] -> ->.
  case/boolP : (p \in d) => X.
  + eapply ex_intro.
    constructor.
    apply exec0_lw with p => //.
    rewrite heap.get_proj //.
    by apply Hz.
  + eapply ex_intro.
    constructor.
    apply exec0_lw_error.
    move=> [l [Hl [p_ Hp_]]].
    rewrite Hp in Hl.
    have {Hl}Y : p = l by lia.
    subst l.
    by rewrite heap.get_proj_None in Hp_.
- move=> st h rt off base Hcond st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  apply exec0_lw_error.
  contradict Hcond.
  case: Hcond => l [Hl [z Hz]]; exists l; split=> //.
  exists z.
  case/boolP : (l \in d) => X.
  + by rewrite heap.get_proj in Hz.
  + by rewrite heap.get_proj_None in Hz.
- move=> st h rt idx base p z Hp Hz st_ h_ d [] -> ->.
  case/boolP : (p \in d) => X.
  + eapply ex_intro.
    constructor.
    apply exec0_lwxs with p => //.
    rewrite heap.get_proj //.
    by apply Hz.
  + eapply ex_intro.
    constructor.
    apply exec0_lwxs_error.
    move=> [l [Hl [p_ Hp_]]].
    rewrite Hp in Hl.
    have {Hl}Y : p = l by lia.
    subst l.
    by rewrite heap.get_proj_None in Hp_.
- move=> st h rt off base Hcond st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  apply exec0_lwxs_error.
  contradict Hcond.
  case: Hcond => l [Hl [z Hz]]; exists l; split=> //.
  exists z.
  case/boolP : (l \in d) => X.
  + by rewrite heap.get_proj in Hz.
  + by rewrite heap.get_proj_None in Hz.
- move=> st h rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_maddu.
- move=> st h rd st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_mfhi.
- move=> st h rd st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_mflhxu.
- move=> st h rd st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_mflo.
- move=> st h rd rs rt Hcond st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_movn_true.
- move=> st h rd rs rt Hcond st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_movn_false.
- move=> st h rd rs rt Hcond st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_movz_true.
- move=> st h rd rs rt Hcond st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_movz_false.
- move=> st h rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_msubu.
- move=> st h rd st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_mthi.
- move=> st h rd st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_mtlo.
- move=> st h rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_multu.
- move=> st h rd rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_nor.
- move=> st h rd rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_or.
- move=> st h rx ry sa st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_sll.
- move=> st h rd rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_sllv.
- move=> st h rd rs rt flag Hflag st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_sltu.
- move=> st h rd rt sa st_ h_ d [] -> ->.
  eapply ex_intro.
  by apply while.exec_cmd0, exec0_sra.
- move=> st h rd rt sa st_ h_ d [] -> ->.
  eapply ex_intro.
  by apply while.exec_cmd0, exec0_srl.
- move=> st h rd rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_srlv.
- move=> st h rd rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_subu.
- move=> st h rt off base p Hp [z Hz] st_ h_ d [] -> ->.
  case/boolP : (p \in d) => X.
  + eapply ex_intro.
    constructor.
    apply exec0_sw.
    apply Hp.
    exists z.
    by rewrite heap.get_proj.
  + eapply ex_intro.
    constructor.
    apply exec0_sw_err.
    move=> [l [Hl [z' Hz']]].
    have X' : p = l by lia.
    subst p.
    by rewrite heap.get_proj_None in Hz'.
- move=> st h rt off base H st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  apply exec0_sw_err.
  contradict H.
  case: H => [l [Hl [p Hp]]].
  exists l; split => //.
  exists p.
  case/boolP : (l \in d) => X.
  rewrite heap.get_proj // in Hp.
  by rewrite heap.get_proj_None in Hp.
- move=> st h rd rs rt st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_xor.
- move=> st h rt rs imm st_ h_ d [] -> ->.
  eapply ex_intro.
  constructor.
  by apply exec0_xori.
Qed.

Module semop_deter_prop_m := while.While_Semop_Deter_Prop WMIPS_Semop_Deter.

Lemma exec_termi_proj st h s' c d : Some (st, h) -- c ---> s' ->
  exists s'_, Some (st, heap.proj h d) -- c ---> s'_.
Proof.
move Hs : (Some (st, h)) => s.
move=> Hexec.
move: Hexec st h d Hs.
elim=> //; clear c s s'.
- exact exec_termi_proj0.
- move=> s s' s'' c1 c2 Hc1 IHc1 Hc2 IHc2 st h d Hs.
  case: (IHc1 _ _ d Hs) => s1 Hs1.
  destruct s' as [[st' h']|].
  + subst s.
    destruct s1 as [[st1 h1]|].
    * move: (exec_deter_proj _ _ _ _ _ Hc1 _ _ _ Hs1) => Htmp.
      case: Htmp => Hst1 [Hh1 Hd'].
      subst st' h1.
      case: {IHc2}(IHc2 _ _ d (refl_equal _)) => s''_ IHc2.
      exists s''_.
      by eapply while.exec_seq; eauto.
    * exists None.
      eapply while.exec_seq; eauto.
      apply while.exec_none.
  + destruct s''.
    * by move/semop_prop_m.from_none : Hc2.
    * destruct s1 as [[st1 h1]|].
      - move: (safety_monotonicity _ _ _ _ _ Hs1 (heap.difs h d) (map_prop_m.proj_difs_disj_spec _ _)).
        rewrite -heap.proj_difs.
        case=> Hexec _.
        subst s.
        by move: (semop_deter_prop_m.exec_deter _ _ _ Hexec _ Hc1).
      - exists None.
        by eapply while.exec_seq; eauto.
- move=> [st h] s' b c1 c2 Hb Hc1 IHc1 st_ h_ d.
  case=> X Y; subst st_ h_.
  case: (IHc1 _ _ d (refl_equal _)) => s1 Hs1.
  exists s1.
  by apply while.exec_ifte_true.
- move=> [st h] s' b c1 c2 Hb Hc1 IHc1 st_ h_ d.
  case=> X Y; subst st_ h_.
  case: (IHc1 _ _ d (refl_equal _)) => s1 Hs1.
  exists s1.
  by apply while.exec_ifte_false.
- (* while true *) move=> [st h] s' s'' b c Hb Hc IHc Hwhile IHwhile st_ h_ d [] X Y; subst st_ h_.
  case: {IHc}(IHc _ _ d (refl_equal _)) => s1 IHc.
  destruct s1 as [[st1 h1]|].
  + destruct s' as [[st' h']|].
    * move: (exec_deter_proj _ _ _ _ _ Hc _ _ _ IHc) => Htmp.
      case: Htmp => Hst1 [Hh1 Hh'].
      subst st1 h1.
      case: {IHwhile}(IHwhile _ _ d (refl_equal _)) => s' IHwhile.
      exists s'.
      eapply while.exec_while_true => //.
      apply IHc.
      done.
    * move: (safety_monotonicity _ _ _ _ _ IHc (heap.difs h d) (map_prop_m.proj_difs_disj_spec _ _)).
      rewrite -heap.proj_difs.
      case=> Hexec _.
      by move: (semop_deter_prop_m.exec_deter _ _ _ Hexec _ Hc).
  + exists None.
    apply while.exec_while_true with None => //.
    by apply while.exec_none.
- move=> [st h] b c Hb st_ h_ d [] -> ->.
  eapply ex_intro.
  by apply while.exec_while_false.
Qed.

Require Import Epsilon.

Lemma triple_exec_precond c P Q : mips_seplog.WMIPS_Hoare.hoare P c Q ->
  forall st h s', Some (st, h) -- c ---> s' ->
    forall d, P st (heap.proj h d) ->
      {s' | Some (st,h) -- c ---> Some s' }.
Proof.
move=> Hhoare st h s' Hexec d HP.
apply constructive_indefinite_description.
move/hoare_prop_m.soundness : Hhoare.
rewrite /hoare_semantics.
move/(_ _ _ HP) => [Hno_err Hsome].
destruct s' as [p|].
by exists p.
move: (exec_termi_proj _ _ _ _ d Hexec).
case => x Hx.
destruct x as [[st' h']|] => //.
move: (safety_monotonicity _ _ _ _ _ Hx (heap.difs h d) (map_prop_m.proj_difs_disj_spec _ _)).
rewrite -heap.proj_difs.
case=> H1 H2.
by move: (semop_deter_prop_m.exec_deter _ _ _ Hexec _ H1).
Qed.

(* NB: inelegant *)
Definition is_while (c : @while.cmd cmd0 expr_b) : bool :=
  match c with | while.while _ _ => true | _ => false end.

(* NB: inelegant *)
Fixpoint contains_while (c : @while.cmd cmd0 expr_b) : bool :=
  match c with
    | while.cmd_cmd0 c0 => false
    | c ; d => contains_while c || contains_while d
    | while.ifte _ c d => contains_while c || contains_while d
    | while.while _ c => true
  end.

Lemma no_while_terminate : forall c, ~~ contains_while c ->
  forall s, exists s', (s -- c ---> s').
Proof.
elim=> //.
- move=> c _ [s|].
  + case: (mips_cmd.cmd0_terminate c s) => x Hx.
    exists x. by apply while.exec_cmd0.
  + exists None; by apply while.exec_none.
- move=> c1 IHc1 c2 IHc2.
  rewrite /= negb_or.
  case/andP=> H1 H2 s.
  case: {IHc1 H1}(IHc1 H1 s) => s1 H1.
  case: {IHc2 H2}(IHc2 H2 s1) => s2 H2.
  exists s2; by apply while.exec_seq with s1.
- move=> b c1 IH1 c2 IH2.
  rewrite /= negb_or.
  case/andP=> H1 H2 s.
  destruct s as [[s h]|].
  + case/boolP : (eval_b b s) => Hb.
    * case: {IH1 H1}(IH1 H1 (Some (s, h))) => s1 H1.
      exists s1; by apply while.exec_ifte_true.
    * case: {IH2 H2}(IH2 H2 (Some (s, h))) => s2 H2.
      by exists s2; apply while.exec_ifte_false.
  + exists None; by apply while.exec_none.
Qed.

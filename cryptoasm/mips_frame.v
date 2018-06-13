(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import ZArith_ext machine_int.
Import MachineInt.
Require Import mips_seplog.

Local Close Scope positive_scope.

Local Open Scope heap_scope.
Import expr_m.
Local Open Scope mips_expr_scope.
Local Open Scope mips_cmd_scope.
Import assert_m.
Local Open Scope mips_assert_scope.
Local Open Scope mips_hoare_scope.

(** * Frame rule *)

Definition modified_regs0 (c : cmd0) : seq store.var :=
  match c with
    | nop => nil
    | add rd _ _ => rd :: nil
    | addi rt _ _ => rt :: nil
    | addiu rt _ _ => rt :: nil
    | addu rd _ _ => rd :: nil
    | cmd_and rd _ _ => rd :: nil
    | andi rt _ _ => rt :: nil
    | lw rt _ _  => rt :: nil
    | lwxs rt _ _ => rt :: nil
    | maddu _ _ => nil
    | mflo rd => rd :: nil
    | movn rd _ _ => rd :: nil
    | movz rd _ _ => rd :: nil
    | mfhi rd => rd :: nil
    | mflhxu rd => rd :: nil
    | msubu _ _  => nil
    | mthi _ => nil
    | mtlo _ => nil
    | multu _ _  => nil
    | nor rd _ _ => rd :: nil
    | cmd_or rd _ _ => rd :: nil
    | sll rx _ _ => rx :: nil
    | sllv rd _ _ => rd :: nil
    | sra rd _ _ => rd :: nil
    | srl rd _ _ => rd :: nil
    | srlv rd _ _ => rd :: nil
    | sltu rd _ _ => rd :: nil
    | sw _ _ _ => nil
    | subu rd _ _ => rd :: nil
    | xor rd _ _ => rd :: nil
    | xori rt _ _ => rt :: nil
  end.

Fixpoint modified_regs (c : @while.cmd cmd0 expr_b) : seq store.var :=
  match c with
    | while.cmd_cmd0 c0 => modified_regs0 c0
    | while.while _ c => modified_regs c
    | c1 ; c2 => modified_regs c1 ++ modified_regs c2
    | while.ifte t c1 c2 => modified_regs c1 ++ modified_regs c2
  end.

Lemma inde_seq R c d : inde (modified_regs (c ; d)) R ->
  inde (modified_regs c) R /\ inde (modified_regs d) R.
Proof.
move=> H; split => s h x v H'; split => H''.
- rewrite -H //=; apply List.in_or_app; by left.
- rewrite (H _ _ x v) //=; apply List.in_or_app; by left.
- rewrite -H //=; apply List.in_or_app; by right.
- rewrite (H _ _ x v) //=; apply List.in_or_app; by right.
Qed.

Lemma inde_ifte R t c d : inde (modified_regs (while.ifte t c d)) R ->
  inde (modified_regs c) R /\ inde (modified_regs d) R.
Proof.
move=> H; split => s h x v H'; split => H''.
- rewrite -H //=; apply: List.in_or_app; by left.
- rewrite (H _ _ x v) //=; apply: List.in_or_app; by left.
- rewrite -H //=; apply List.in_or_app; by right.
- rewrite (H _ _ x v) //=; apply List.in_or_app; by right.
Qed.

Definition modifies_mult0 (c : cmd0) :=
  match c with
    | nop => false
    | add _ _ _ => false
    | addi _ _ _ => false
    | addiu _ _ _ => false
    | addu _ _ _ => false
    | cmd_and _ _ _ => false
    | andi _ _ _ => false
    | lw _ _ _ => false
    | lwxs _ _ _ => false
    | maddu _ _ => true
    | mfhi _ => false
    | mflhxu _ => true
    | mflo _ => false
    | movn _ _ _ => false
    | movz _ _ _ => false
    | msubu _ _ => true
    | mtlo _ => true
    | mthi _ => true
    | multu _ _ => true
    | nor _ _ _ => false
    | cmd_or _ _ _ => false
    | sll _ _ _ => false
    | sllv _ _ _ => false
    | sltu _ _ _ => false
    | sra _ _ _ => false
    | srl _ _ _ => false
    | srlv _ _ _ => false
    | subu _ _ _ => false
    | sw _ _ _ => false
    | xor _ _ _ => false
    | xori _ _ _ => false
  end.

Fixpoint modifies_mult (c : @while.cmd cmd0 expr_b) : bool :=
  match c with
    | while.cmd_cmd0 c => modifies_mult0 c
    | while.while _ c' => modifies_mult c'
    | c1 ; c2 => modifies_mult c1 || modifies_mult c2
    | while.ifte t c1 c2 => modifies_mult c1 || modifies_mult c2
  end.

(** an assert that is independent of the execution of a command modifying the multiplier *)
Definition inde_cmd_mult c (P : assert) := modifies_mult c -> inde_mult P.

Lemma inde_cmd_mult_TT : forall l, inde_cmd_mult l TT. Proof. by []. Qed.

Lemma inde_cmd_mult_seq R c d : inde_cmd_mult (c; d) R ->
  inde_cmd_mult c R /\ inde_cmd_mult d R.
Proof.
move=> H; split => H' s h m m'; split => H''.
- by rewrite -(H _ _ _ m) //= H'.
- by rewrite -(H _ _ _ m') //= H'.
- by rewrite -(H _ _ _ m) //= H' orbC.
- by rewrite -(H _ _ _ m') //= H' orbC.
Qed.

Lemma inde_cmd_mult_ifte R t c d : inde_cmd_mult (while.ifte t c d) R ->
  inde_cmd_mult c R /\ inde_cmd_mult d R.
Proof.
move=> H; split => H' s h m m'; split => H''.
- by rewrite -(H _ _ _ m) //= H'.
- by rewrite -(H _ _ _ m') //= H'.
- by rewrite -(H _ _ _ m) //= H' orbC.
- by rewrite -(H _ _ _ m') //= H' orbC.
Qed.

Lemma frame_rule0 (P Q : assert) (c : cmd0) : {{[ P ]}} c {{[ Q ]}} ->
  forall (R : assert), inde (modified_regs c) R ->
    inde_cmd_mult c R -> {{ P ** R }} c {{ Q ** R }}.
Proof.
elim; clear P Q c.
- (* nop *) move=> P R H1 H2; by do 2 constructor.
- (* add *) move=> Q rs rt rd R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_add rd rs rt (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [H3 [H4 [ [H5 H7] H6] ] ] ] ].
  split => //.
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* addi *)
  move=> Q rt rs imm R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_addi rt rs imm (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [ [H5 H7] H6] ] ] ] ].
  split => //.
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* addiu *) move=> Q rt rs imm R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_addiu rt rs imm (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [ H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* addu *) move=> Q rs rt rd R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_addu rd rs rt (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* cmd_and *) move=> P rd rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_and rd rs rt (P ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* andi *) move=> P rt rs imm R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_andi rt rs imm (P ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* lw *) move=> Q rt offset base R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_lw rt offset base (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [H3 [H4 [ [p [H7 [z [H8 H9] ] ] ] H6] ] ] ] ].
  exists p; split => //.
  exists z; split => //.
  rewrite H4.
  by apply heap.get_union_L.
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* lwxs *) move=> rt index base P0 R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_lwxs rt index base (P0 ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [H3 [H4 [ [p [H7 [z [H8 H9] ] ] ] H6] ] ] ] ].
  exists p; split => //.
  exists z; split => //.
  rewrite H4.
  by apply heap.get_union_L.
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* maddu *) move=> Q rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_maddu rs rt (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by rewrite -(H2 _ s h2 m).
- (* mfhi *) move=> Q rd R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_mfhi rd (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* mflhxu *) move=> rd Q R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_mflhxu rd (Q ** R))); last by do 2 constructor.
  move=> [s [a [hi lo]]] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  rewrite /=.
  case: ifP => [/eqP ? | X].
  + rewrite -(H2 _ _ _) //; by apply H6.
  + have : List.In rd (modified_regs (mflhxu rd)) by rewrite /=; auto.
    move/(H1 (s, (a, (hi, lo))) h2 rd lo).
    rewrite /store.upd X => {H1}H1.
    rewrite -(H2 _ _ _ (a, (hi, lo))) //; tauto.
- (* mflo *) move=> Q rd R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_mflo rd (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* movn *) move=> Q rd rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_movn rd rs rt (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  split => H7.
  exists h1, h2; repeat (split => //).
  by apply (proj1 H5).
  by apply inde_upd_store.
  exists h1, h2; repeat (split => //).
  by apply (proj2 H5).
- (* movz *) move=> Q rd rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_movz rd rs rt (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  split => H7.
  exists h1, h2; repeat (split => //).
  by apply (proj1 H5).
  by apply inde_upd_store.
  exists h1, h2; repeat (split => //).
  by apply (proj2 H5).
- (* msubu *) move=> Q rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_msubu rs rt (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by rewrite -(H2 _ s h2 m).
- (* mthi *) move=> Q rs R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_mthi rs (Q ** R))); last by do 2 constructor.
  move=> [s [a [hi lo]]] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  rewrite /= -(H2 _ _ _) //.
  by apply H6.
- (* mtlo *) move=> Q rs R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_mtlo rs (Q ** R))); last by do 2 constructor.
  move=> [s [a [hi lo]]] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  rewrite /= -(H2 _ s h2) //.
  by apply H6.
- (* multu *) move=> Q rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_multu rs rt (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by rewrite /= -(H2 _ s h2 m).
- (* nor *) move=> Q rd rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_nor rd rs rt (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* or *) move=> Q rd rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_or rd rs rt (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* sll *) move=> Q rx ry sa R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_sll rx ry sa (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* sllv *) move=> Q rd rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_sllv rd rs rt (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* sltu *) move=> Q rd rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_sltu rd rs rt (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* sra *) move=> Q rd rt sa R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_sra rd rt sa (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* srl *) move=> Q rd rt sa R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_srl rd rt sa (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [ H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* srlv *) move=> Q rd rt rs R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_srlv rd rt rs (Q ** R))); last by do 2 constructor.
  move=> [s m] h [h1 [h2 [H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* subu *) move=> Q rs rt rd R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_subu rd rs rt (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [H3 [H4 [H5 H6] ] ] ] ].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* sw *) move=> rt off b Q R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_sw rt off b (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [ [p [H7 [ [z H8] H9]]] H6]]]]].
  exists p; split => //.
  split.
  exists z.
  rewrite H4.
  by apply heap.get_union_L.
  exists (heap.upd p [rt]_s h1), h2; split.
  by apply heap.disj_upd.
  split => //.
  rewrite H4.
  by apply heap.upd_union_L with z.
- (* xor *) move=> Q rd rs rt R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_xor rd rs rt (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [H5 H6]]]]].
  exists h1, h2; repeat (split => //).
  by apply inde_upd_store.
- (* xori *) move=> Q rt rs imm R H1 H2.
  apply (hoare_prop_m.hoare_stren (wp_xori rt rs imm (Q ** R))); last by do 2 constructor.
  move=> s h [h1 [h2 [ H3 [H4 [H5 H6]]]]].
  exists h1, h2; repeat (split=> //).
  by apply inde_upd_store.
Qed.

Lemma frame_rule_R (P : assert) c (Q : assert) : {{ P }} c {{ Q }} -> 
  forall (R : assert), inde (modified_regs c) R -> inde_cmd_mult c R ->
    {{ P ** R }} c {{ Q ** R }}.
Proof.
elim; clear P c Q.
- exact frame_rule0.
- (* seq *) move=> Q P R c d H IHhoare1 H0 IHhoare2 U.
  case/inde_seq => H11 H12.
  case/inde_cmd_mult_seq => H21 H22.
  apply (while.hoare_seq _ _ _ _ _ _ (Q ** U)); by [apply IHhoare1 | apply IHhoare2].
- (* conseq *) move=> P P' Q Q' c H H0 H1 IHhoare R H2 H3.
  move: (IHhoare _ H2 H3) => H4.
  apply (hoare_prop_m.hoare_stren (P' ** R)).
  move=> s h [h1 [h2 [H5 [H6 [H7 H8]]]]]; by exists h1, h2; auto.
  apply (hoare_prop_m.hoare_weak (Q' ** R)) => //.
  move=> s h [h1 [h2 [ H5 [H6 [H7 H8]]]]]; by exists h1, h2; auto.
- (* while *) move=> P t c H IHhoare R H1 H2.
  apply (hoare_prop_m.hoare_weak (fun s h => (P ** R) s h /\ ~~ eval_b t s)).
  move=> s h [[h1 [h2 [H3 [H4 [H5 H6]]]]] H7]; by exists h1, h2.
  apply (hoare_prop_m.hoare_stren (P ** R)) => //.
  apply while.hoare_while with (P := P ** R).
  move: (IHhoare _ H1 H2) => H3.
  apply (hoare_prop_m.hoare_stren (fun s h => ((fun s0 h0 => P s0 h0 /\ eval_b t s) ** R) s h)) => //.
  move=> s h [ [h1 [h2 [ H4 [H5 [H6 H7] ] ] ] ] H8 ]; by exists h1, h2.
- (* ifte *) move=> P Q t c d H1 IHhoare1 H3 IHhoare2 R.
  case/inde_ifte => H51 H52.
  case/inde_cmd_mult_ifte => H61 H62.
  apply while.hoare_ifte.
  + apply (hoare_prop_m.hoare_stren ((fun s h => P s h /\ eval_b t s) ** R)).
    move=> s h [ [h1 [h2 [H8 [H9 [H10 H11] ] ] ] ] H12 ]; by exists h1, h2.
    by apply IHhoare1.
  + apply (hoare_prop_m.hoare_stren ((fun s h => P s h /\ ~~ eval_b t s) ** R)).
    move=> s h [ [h1 [h2 [H8 [H9 [H10 H11] ] ] ] ] H12 ]; by exists h1, h2.
    by apply IHhoare2.
Qed.

Lemma frame_rule_L (P : assert) (c : while.cmd) (Q : _assert) : {{P}}c {{Q}} ->
  forall R : assert, inde (modified_regs c) R ->
    inde_cmd_mult c R -> {{R ** P}}c {{R ** Q}}.
Proof.
move=> P_c_Q R H1 H2.
apply (while.hoare_conseq _ _ _ _ _ _ _ (P ** R) _ (Q ** R)).
by rewrite assert_m.conCE.
by rewrite assert_m.conCE.
by apply frame_rule_R.
Qed.

Lemma before_frame R P' Q' P c Q : {{ P' ** R }} c {{ Q' ** R }} ->
  P ===> P' ** R -> Q' ** R ===> Q -> {{ P }} c {{ Q }}.
Proof. move=> H1 H2 H3; by eapply while.hoare_conseq; eauto. Qed.


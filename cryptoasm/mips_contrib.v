(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool.
Require Import machine_int.
Import MachineInt.
Require Import mips_seplog mips_frame mips_tactics.

Local Open Scope heap_scope.
Import expr_m.
Local Open Scope mips_expr_scope.
Import assert_m.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.

Lemma cell_read e v Q s h : (e |~> v ** TT) s h /\ Q s h ->
 (e |~> v ** (e |~> v -* Q)) s h.
Proof.
move=> [[h1 [h2 [Hdisj [Hunion [Hev _]]]]] HQ].
exists h1, h2; repeat (split; trivial).
move=> h2' [Hdisj2 Hev'] h'' Hunion2.
rewrite Hunion2 -(singl_equal _ _ _ _ _ _ _ Hev Hev') // heap.unionC //.
by rewrite -Hunion.
by apply heap.disj_sym.
Qed.

(** Various Derived Hoare triples *)

Lemma hoare_nop' P Q : P ===> Q -> {{ P }} nop {{ Q }}.
Proof. move=> H; apply (hoare_prop_m.hoare_stren Q) => //; by do 2 constructor. Qed.

Lemma hoare_addi' P Q rt rs i : P ===> wp_addi rt rs i Q -> 
  {{ P }} addi rt rs i {{ Q }}.
Proof. 
move=> H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done. 
Qed.

Lemma hoare_addi R P Q rt rs i c : P ===> wp_addi rt rs i R -> 
  {{ R }} c {{ Q }} -> {{ P }} addi rt rs i ; c {{ Q }}.
Proof. move=> H H'; econstructor; eauto; by apply hoare_addi'. Qed.

Lemma hoare_addiu' P Q rt rs i : P ===> wp_addiu rt rs i Q -> 
  {{ P }} addiu rt rs i {{ Q }}.
Proof. move=> H; eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done. Qed.

Lemma hoare_addiu R P Q rt rs i c : P ===> wp_addiu rt rs i R -> 
  {{ R }} c {{ Q }} -> {{ P }} addiu rt rs i ; c {{ Q }}.
Proof. move=> H H'. econstructor; eauto; by apply hoare_addiu'. Qed.

Local Open Scope machine_int_scope.

Definition FunAndAddiu P i v (iv : immediate) : assert :=
  fun s h => P s h /\ u2Z [i]_s = u2Z ([v]_s `+ sext 16 iv).

Ltac NextAddiu :=
  match goal with 
    | |- {{ ?P }} (cmd_cmd0_coercion (addiu ?J ?V ?IV) ; ?C) {{ ?Q }} =>
      let tmp := (eval cbv beta in (FunAndAddiu P J V IV)) in
	apply hoare_addiu with tmp; [unfold FunAndAddiu | idtac]
    | |- WMIPS_Hoare.hoare ?P (cmd_cmd0_coercion (addiu ?J ?V ?IV) ; ?C) ?Q =>
      let tmp := (eval cbv beta in (FunAndAddiu P J V IV)) in
	apply hoare_addiu with tmp; [unfold FunAndAddiu | idtac]
  end.
(* TODO: strange : in bbs_triple, the notation {{ cannot be displayed
   anymore causing this tactics to fail without the second case ;
   move to mips_tactics? *)

Local Close Scope machine_int_scope.

Lemma hoare_add' P Q rd rs rt : P ===> wp_add rd rs rt Q -> 
  {{ P }} add rd rs rt {{ Q }}.
Proof. move=> H. eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done. Qed.

Lemma hoare_addu' P Q rd rs rt : P ===> wp_addu rd rs rt Q -> 
  {{ P }} addu rd rs rt {{ Q }}.
Proof. move=> H. eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done. Qed.

Lemma hoare_addu R P Q rd rs rt c : P ===> wp_addu rd rs rt R ->
  {{ R }} c {{ Q }} -> {{ P }} addu rd rs rt ; c {{ Q }}.
Proof. move=> H H'. econstructor; eauto; by apply hoare_addu'. Qed.

Lemma hoare_and' P Q rd rs rt : P ===> wp_and rd rs rt Q -> 
  {{ P }} cmd_and rd rs rt {{ Q }}.
Proof. move=> H. eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done. Qed.

Lemma hoare_and : forall R P Q rd rs rt c, P ===> wp_and rd rs rt R -> 
  {{ R }} c {{ Q }} -> {{ P }} cmd_and rd rs rt ; c {{ Q }}.
Proof.
move=> R P Q rd rs rt c H H'.
econstructor; eauto; apply hoare_and' => //.
Qed.

Lemma hoare_andi' : forall P Q rt rs imm, P ===> wp_andi rt rs imm Q -> 
  {{ P }} andi rt rs imm {{ Q }}.
Proof.
move=> P Q rt rs imm H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
Qed.

Lemma hoare_andi : forall R P Q rt rs imm c, P ===> wp_andi rt rs imm R -> 
  {{ R }} c {{ Q }} -> {{ P }} andi rt rs imm ; c {{ Q }}.
Proof.
move=> R P Q rt rs imm c H H'.
econstructor; eauto; apply hoare_andi' => //.
Qed.

Lemma hoare_lw' : forall rt (index : immediate) base P Q,
  (P ===> wp_lw rt index base Q) ->
  {{ P }} lw rt index base {{ Q }}.
Proof.
move=> rt idx base P Q H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Definition update_store_lw rt v P : assert := fun s h => P (store.upd rt v s) h.

Lemma hoare_lw_back : forall rt (idx : immediate) base Q,
  {{ fun s h => exists e,
    (var_e base \+ int_e (sext 16 idx) |~> int_e e **
      (var_e base \+ int_e (sext 16 idx) |~> int_e e -* 
	(update_store_lw rt e Q))) s h }} lw rt idx base {{ Q }}.
Proof.
move=> rt idx base Q.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
move=> s h [x H].
generalize (assert_m.mp _ _ _ _ H) => Hmp.
move: H => [h1 [h2 [Hdisj [Hunion [ [p [Hp1 Hp2] ] H2] ] ] ] ].
exists p; split => //.
exists ([ int_e x ]e_ s); split => //.
rewrite Hunion; apply heap.get_union_L => //.
by rewrite Hp2 heap.get_sing.
Qed.

Lemma hoare_lw_back'' : forall rt (idx : immediate) base P Q R c,
  P ===> (fun s h => exists e,
    (var_e base \+ int_e (sext 16 idx) |~> int_e e **
      ((var_e base \+ int_e (sext 16 idx) |~> int_e e) -* 
	(update_store_lw rt e R))) s h) ->
  {{ R }} c {{ Q }} -> {{ P }} lw rt idx base; c {{ Q }}.
Proof.
move=> rt idex base P Q R c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; eauto.
by apply hoare_lw_back.
Qed.

Lemma hoare_lw_back_alt'' : forall rt (idx : immediate) base P Q R c,
  P ===> (fun s h => exists e,
    (var_e base \+ int_e (sext 16 idx) |~> int_e e ** TT) s h /\      
    (update_store_lw rt e R) s h) ->
  {{ R }} c {{ Q }} -> {{ P }} lw rt idx base; c {{ Q }}.
Proof.
move=> rt idx base P Q R c H H'.
apply hoare_lw_back'' with R => //.
move=> s h H''.
move: (H _ _ H'') => [x H2].
exists x; by apply cell_read.
Qed.

Lemma hoare_lwxs' : forall rt idx base P Q, P ===> wp_lwxs rt idx base Q ->
  {{ P }} lwxs rt idx base {{ Q }}.
Proof.
move=> rt idx base P Q H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_lwxs : forall R P Q rt idx base c, P ===> wp_lwxs rt idx base R -> 
  {{ R }} c {{ Q }} -> {{ P }} lwxs rt idx base ; c {{ Q }}.
Proof.
move=> R P Q rt idx base c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; eauto.
by do 2 constructor.
Qed.

Definition update_store_lwxs rt v P : assert := fun s h => P (store.upd rt v s) h.

Lemma hoare_lwxs_back : forall rt idx base P,
  {{ fun s h => exists e, 
    (var_e base \+ shl2_e (var_e idx) |~> int_e e ** 
      (var_e base \+ shl2_e (var_e idx) |~> int_e e -* 
	(update_store_lwxs rt e P))) s h }} lwxs rt idx base {{ P }}.
Proof.
move=> rt idx base P.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
move=> s h [x H].
generalize (assert_m.mp _ _ _ _ H) => Hmp.
move: H => [h1 [h2 [Hdisj [Hunion [ [p [Hp1 Hp2] ] H2] ] ] ] ].
exists p; split => //.
exists ([ int_e x ]e_ s); split => //.
rewrite Hunion; apply heap.get_union_L => //.
by rewrite Hp2 heap.get_sing.
Qed.

Lemma hoare_lwxs_back' : forall rt idx base P Q,
  P ===> (fun s h => exists e,
    (var_e base \+ shl2_e (var_e idx) |~> int_e e **
      ((var_e base \+ shl2_e (var_e idx) |~> int_e e) -* 
	update_store_lwxs rt e Q)) s h) ->
  {{P}} lwxs rt idx base {{ Q }}.
Proof.
move=> rt idx base P Q H.
eapply hoare_prop_m.hoare_stren; eauto.
by apply hoare_lwxs_back.
Qed.

Lemma hoare_lwxs_back'' : forall rt idx base P Q R c,
  P ===> (fun s h => exists e,
    (var_e base \+ shl2_e (var_e idx) |~> int_e e **
      ((var_e base \+ shl2_e (var_e idx) |~> int_e e) -* 
	update_store_lwxs rt e R)) s h) ->
  {{ R }} c {{ Q }} -> {{ P }} lwxs rt idx base; c {{ Q }}.
Proof.
move=> rt idx base P Q R c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; eauto.
by apply hoare_lwxs_back.
Qed.

Lemma hoare_lwxs_back_alt': forall rt idx base P Q,
  P ===> (fun s h => exists e,
    (var_e base \+ shl2_e (var_e idx) |~> int_e e ** TT) s h /\
    (update_store_lwxs rt e Q) s h) ->
  {{ P }} lwxs rt idx base {{ Q }}.
Proof.
move=> rt idx base P Q H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
move=> s h H0.
move: (H _ _ H0) => [e [ [h1 [h2 [H1 [H2 [ [x [H6 H7] ] H4] ] ] ] ] H5] ].
exists x; split => //.
exists e; split => //.
rewrite H2.
apply heap.get_union_L => //.
by rewrite H7 heap.get_sing.
Qed.

Lemma hoare_lwxs_back_alt'': forall rt idx base P Q R c,
  P ===> (fun s h => exists e,
    ((var_e base \+ shl2_e (var_e idx) |~> int_e e) ** TT) s h /\
    (update_store_lwxs rt e R) s h) ->
  {{ R }} c {{ Q }} -> {{ P }} lwxs rt idx base; c {{ Q }}.
Proof.
move=> rt idx base P Q R c H H'.
apply while.hoare_seq with R => //.
by apply hoare_lwxs_back_alt'.
Qed.

Lemma hoare_maddu' : forall P Q rs rt, P ===> wp_maddu rs rt Q -> 
  {{ P }} maddu rs rt {{ Q }}.
Proof.
move=> P Q rs rt H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
Qed.

Lemma hoare_maddu : forall P Q R rs rt c, P ===> wp_maddu rs rt R ->
  {{ R }} c {{ Q }} -> {{ P }} maddu rs rt ; c {{ Q }}.
Proof.
move=> P Q R rs rt c H H'.
apply while.hoare_seq with R => //.
by apply hoare_maddu'.
Qed.

Lemma hoare_mflhxu' : forall P Q rd, P ===> wp_mflhxu rd Q -> 
  {{ P }} mflhxu rd {{ Q }}.
Proof.
move=> P Q rd H.
eapply hoare_prop_m.hoare_stren; eauto.
do 2 constructor.
Qed.

Lemma hoare_mflhxu : forall R P Q rd c, P ===> wp_mflhxu rd R -> 
  {{ R }} c {{ Q }} -> {{ P }} mflhxu rd ; c {{ Q }}.
Proof.
move=> R P Q rd c H H'.
eapply while.hoare_seq; eauto.
eapply hoare_mflhxu'; eauto.
Qed.

Lemma hoare_mfhi' : forall P Q rd, P ===> wp_mfhi rd Q -> 
  {{ P }} mfhi rd {{ Q }}.
Proof.
move=> P Q rd H.
eapply hoare_prop_m.hoare_stren; eauto.
by do 2 constructor.
Qed.

Lemma hoare_mfhi : forall P Q R rd c, P ===> wp_mfhi rd R -> 
  {{ R }} c {{ Q }} -> {{ P }} mfhi rd ; c {{ Q }}.
Proof.
move=> P Q R rd c H H'.
eapply while.hoare_seq; eauto.
eapply hoare_mfhi'; eauto.
Qed.

Lemma hoare_mflo' : forall P Q rd, P ===> wp_mflo rd Q -> 
  {{ P }} mflo rd {{ Q }}.
Proof. move=> P Q rd H. eapply hoare_prop_m.hoare_stren; eauto. by do 2 constructor. Qed.

Lemma hoare_mflo : forall P Q R rd c, P ===> wp_mflo rd R -> 
  {{ R }} c {{ Q }} -> {{ P }} mflo rd ; c {{ Q }}.
Proof.
move=> P Q R rd c H H'.
eapply while.hoare_seq; eauto.
eapply hoare_mflo'; eauto.
Qed.

Lemma hoare_movn' : forall P Q rd rs rt, P ===> wp_movn rd rs rt Q ->
  {{ P }} movn rd rs rt {{ Q }}.
Proof.
move=> P Q rd rs rt H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_movn : forall P Q R rd rs rt c, P ===> wp_movn rd rs rt R ->
  {{ R }} c {{ Q }} -> {{ P }} movn rd rs rt ; c {{ Q }}.
Proof.
move=> P Q R rd rs rt c0 H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_movz' : forall P Q rd rs rt, P ===> wp_movz rd rs rt Q -> 
  {{ P }} movz rd rs rt {{ Q }}.
Proof.
move=> P Q rd rs rt H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_movz : forall P Q R rd rs rt c, P ===> wp_movz rd rs rt R ->
  {{ R }} c {{ Q }} -> {{ P }} movz rd rs rt ; c {{ Q }}.
Proof.
move=> P Q R rd rs rt c0 H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_mthi' : forall P Q rs, P ===> wp_mthi rs Q -> 
  {{ P }} mthi rs {{ Q }}.
Proof.
move=> P Q rd H.
eapply hoare_prop_m.hoare_stren; eauto.
do 2 constructor.
Qed.

Lemma hoare_mthi : forall P Q R rs c, P ===> wp_mthi rs R -> 
  {{ R }} c {{ Q }} -> {{ P }} mthi rs ; c {{ Q }}.
Proof.
move=> P Q R rs c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_mtlo' : forall P Q rs, P ===> wp_mtlo rs Q -> 
  {{ P }} mtlo rs {{ Q }}.
Proof.
move=> P Q rs H.
eapply hoare_prop_m.hoare_stren; eauto.
do 2 constructor.
Qed.

Lemma hoare_mtlo : forall P Q R rs c, P ===> wp_mtlo rs R -> 
  {{ R }} c {{ Q }} -> {{ P }} mtlo rs ; c {{ Q }}.
Proof.
move=> P Q R rs c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_msubu' : forall P Q rs rt, P ===> wp_msubu rs rt Q -> 
  {{ P }} msubu rs rt {{ Q }}.
Proof.
intros.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.
  
Lemma hoare_msubu : forall P Q R rs rt c, P ===> wp_msubu rs rt R ->
  {{ R }} c {{ Q }} -> {{ P }} msubu rs rt ; c {{ Q }}.
Proof.
move=> P Q R rs rt c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.  

Lemma hoare_multu' : forall P Q rs rt, P ===> wp_multu rs rt Q ->
  {{ P }} multu rs rt {{ Q }}.
Proof.
move=> P Q rs rt H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_multu : forall P Q R rs rt c, P ===> wp_multu rs rt R ->
  {{ R }} c {{ Q }} -> {{ P }} multu rs rt ; c {{ Q }}.
Proof.
move=> P Q R rs rt c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_nor' : forall P Q rd rs rt, P ===> wp_nor rd rs rt Q -> 
  {{ P }} nor rd rs rt {{ Q }}.
Proof.
move=> P Q rd rs rt H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_or' : forall P Q rd rs rt, P ===> wp_or rd rs rt Q -> 
  {{ P }} cmd_or rd rs rt {{ Q }}.
Proof.
move=> P Q rd rs rt H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_or : forall R P Q rd rs rt c, P ===> wp_or rd rs rt R -> 
  {{ R }} c {{ Q }} -> {{ P }} cmd_or rd rs rt ; c {{ Q }}.
Proof.
move=> R P Q rd rs rt c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_sll' : forall P Q rx ry sa, P ===> wp_sll rx ry sa Q -> 
  {{ P }} sll rx ry sa {{ Q }}.
Proof.
move=> P Q rx ry sa H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_sll : forall R P Q rd rs sa c, P ===> wp_sll rd rs sa R -> 
  {{ R }} c {{ Q }} -> {{ P }} sll rd rs sa ; c {{ Q }}.
Proof.
move=> R P Q rd rs sa c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_sllv' : forall P Q rd rs rt, P ===> wp_sllv rd rs rt Q -> 
  {{ P }} sllv rd rs rt {{ Q }}.
Proof.
move=> P Q rd rs rt H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_sllv : forall R P Q rd rs rt c, P ===> wp_sllv rd rs rt R -> 
  {{ R }} c {{ Q }} -> {{ P }} sllv rd rs rt ; c {{ Q }}.
Proof.
move=> R P Q rd rs rt c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_sra' : forall P Q rx ry ra, P ===> wp_sra rx ry ra Q -> 
  {{ P }} sra rx ry ra {{ Q }}.
Proof.
move=> P Q rd rt sa H.
eapply hoare_prop_m.hoare_stren; by [apply H | do 2 constructor].
Qed.

Lemma hoare_sra : forall R P Q rd rs sa c, P ===> wp_sra rd rs sa R -> 
  {{ R }} c {{ Q }} -> {{ P }} sra rd rs sa ; c {{ Q }}.
Proof.
move=> R P Q rd rs sa c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; by [apply H | do 2 constructor].
Qed.

Lemma hoare_srl' : forall P Q rx ry ra, P ===> wp_srl rx ry ra Q -> 
  {{ P }} srl rx ry ra {{ Q }}.
Proof.
move=> P Q rd rt sa H.
eapply hoare_prop_m.hoare_stren; by [apply H | do 2 constructor].
Qed.

Lemma hoare_srl : forall R P Q rd rs sa c, P ===> wp_srl rd rs sa R -> 
  {{ R }} c {{ Q }} -> {{ P }} srl rd rs sa ; c {{ Q }}.
Proof.
move=> R P Q rd rs sa c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; by [apply H | do 2 constructor].
Qed.

Lemma hoare_srlv' : forall P Q rd rs rt, P ===> wp_srlv rd rs rt Q -> 
  {{ P }} srlv rd rs rt {{ Q }}.
Proof.
move=> P Q rd rs rt H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_srlv : forall R P Q rd rs rt c, P ===> wp_srlv rd rs rt R -> 
  {{ R }} c {{ Q }} -> {{ P }} srlv rd rs rt ; c {{ Q }}.
Proof.
move=> R P Q rd rs rt c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_sltu' : forall P Q rd rs rt, P ===> wp_sltu rd rs rt Q -> 
  {{ P }} sltu rd rs rt {{ Q }}.
Proof.
move=> P Q rd rs rt H.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_sltu : forall R P Q rd rs rt c, P ===> wp_sltu rd rs rt R -> 
  {{ R }} c {{ Q }} -> {{ P }} sltu rd rs rt ; c {{ Q }}.
Proof.
move=> R P Q rd rs rt c H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.  

Lemma hoare_sw' : forall P Q rt off base, P ===> wp_sw rt off base Q -> 
  {{ P }} sw rt off base {{ Q }}.
Proof.
move=> P Q rt off base H.
eapply hoare_prop_m.hoare_stren; eauto.
do 2 constructor.
Qed.

Lemma hoare_sw'' : forall R P Q rt off base c, P ===> wp_sw rt off base R -> 
  {{ R }} c {{ Q }} -> {{ P }} sw rt off base ; c {{ Q }}.
Proof.
move=> R P Q rt off base c H H'.
apply while.hoare_seq with R => //.
by apply hoare_sw'.
Qed.

Lemma hoare_sw_global : forall P rt (idx : immediate) base,
  {{ (fun s h => exists e'', (var_e base \+ int_e (sext 16 idx) |~> e'') s h) ** P }} 
  sw rt idx base 
  {{ (var_e base) \+ int_e (sext 16 idx) |~> var_e rt ** P }}.
Proof.
move=> P rt idx base.
apply frame_rule_R; last 2 first.
  rewrite /inde => s h x v /=; tauto.
  done.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
move=> s h [x [x0 [H1 H2]]].
exists x0; split => //.
split.
- exists ([ x ]e_ s); by rewrite H2 heap.get_sing.
- exists x0; split => //; by rewrite H2 heap.upd_sing.
Qed.

Lemma hoare_sw_back rt (idx : immediate) base Q :
  {{ fun s h => exists e,
    (var_e base \+ int_e (sext 16 idx) |~> e **
      (var_e base \+ int_e (sext 16 idx) |~> var_e rt -* Q)) s h }}
  sw rt idx base {{ Q }}.
Proof.
apply (hoare_prop_m.hoare_stren (wp_sw rt idx base Q)); last by do 2 constructor.
move=> s h [x [h1 [h2 [Hdisj [Hunion [ [p [H1p H1] ] H2] ] ] ]  ] ].
exists p; split => //.
split.
- exists ([ x ]e_ s).
  rewrite Hunion.
  apply heap.get_union_L => //.
  by rewrite H1 heap.get_sing. 
- apply H2 with (heap.upd p [rt]_s h1).
  + split.
    * by apply heap.disj_sym, heap.disj_upd.
    * exists p; split => //.
      by rewrite H1 heap.upd_sing.
  + rewrite Hunion.
    eapply trans_eq.
    * eapply heap.upd_union_L => //.
      rewrite H1 heap.get_sing; reflexivity.
    * rewrite heap.unionC //.
      by apply heap.disj_upd.
Qed.
(* an alternative proof using the frame rule:
intros.
generalize (hoare_sw_global 
  (add_e (var_e base) (int_e (sext_16_32 idx))
         |~> var_e rt -* Q) rt idx base); intro.
apply hoare_weaken_post with (
  ((add_e (var_e base) (int_e (sext_16_32 idx))
         |~> var_e rt) **
  (add_e (var_e base) (int_e (sext_16_32 idx))
         |~> var_e rt -* Q))
  ).
apply assert_m.mp.
apply hoare_prop_m.hoare_stren with (
(fun s1 s2 m h => exists e'', (add_e (var_e base) (int_e (sext_16_32 idx))
         |~> e'') s1 s2 m h) ** (add_e (var_e base) (int_e (sext_16_32 idx))
         |~> var_e rt -* Q)).
red; intros.
inversion_clear H0.
red.
inversion_clear H1 as [h1].
inversion_clear H0 as [h2].
decompose [and] H1; clear H1.
exists h1; exists h2.
split; auto.
split; auto.
split.
exists x.
auto.
auto.
auto.
Qed.
*)

Lemma hoare_sw_back' rt (idx : immediate) base P Q :
  P ===> (fun s h => exists e,
    (var_e base \+ int_e (sext 16 idx) |~> e **
      ((var_e base \+ int_e (sext 16 idx) |~> var_e rt) -* Q)) s h) ->
  {{ P }} sw rt idx base {{ Q }}.
Proof.
move=> H.
eapply hoare_prop_m.hoare_stren; eauto.
by apply hoare_sw_back.
Qed.

Lemma hoare_sw_back'' : forall rt (idx : immediate) base P Q R c,
  P ===> (fun s h => exists e,
    (var_e base \+ int_e (sext 16 idx) |~> e **
      (var_e base \+ int_e (sext 16 idx) |~> var_e rt -* R)) s h) ->
  {{ R }} c {{ Q}} -> {{ P }} sw rt idx base ; c {{ Q }}.
Proof.
move=> rt idx base P Q R c H H'.
apply while.hoare_seq with R; last by done.
by apply hoare_sw_back'.
Qed.

Lemma hoare_sw_global_alt : forall P rt (idx : immediate) base,
  {{ (fun s h => exists e, (var_e base \+ int_e (sext 16 idx) |~> e ) s h) ** P }} 
  sw rt idx base
  {{ (var_e base \+ int_e (sext 16 idx) |~> var_e rt) ** P }}.
Proof.
move=> P rt idx base.
apply frame_rule_R; last 2 first.
  rewrite /inde => s h x v /=; tauto.
  done.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
move=> s h [x [x0 [H1 H2]] ].
exists x0; split => //.
split.
- exists ([ x ]e_ s); by rewrite H2 heap.get_sing.
- exists x0; split => //; by rewrite H2 heap.upd_sing.
Qed.

Lemma hoare_subu' : forall P Q rd rs rt, P ===> wp_subu rd rs rt Q -> 
  {{ P }} subu rd rs rt {{ Q }}.
Proof.
intros.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_subu : forall P Q R rd rs rt c, P ===> wp_subu rd rs rt R ->
  {{ R }} c {{ Q }} -> {{ P }} subu rd rs rt ; c {{ Q }}.
Proof.
move=> P Q R rd rs rt c0 H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_xor' : forall P Q rd rs rt, P ===> wp_xor rd rs rt Q -> 
  {{ P }} xor rd rs rt {{ Q }}.
Proof.
move=> P Q rd rs rt H.
eapply hoare_prop_m.hoare_stren; last first.
do 2 constructor.
done.
Qed.

Lemma hoare_xor : forall P Q R rd rs rt c, P ===> wp_xor rd rs rt R ->
  {{ R }} c {{ Q }} -> {{ P }} xor rd rs rt ; c {{ Q }}.
Proof.
move=> P Q R rd rs rt c0 H H'.
apply while.hoare_seq with R => //.
eapply hoare_prop_m.hoare_stren; last by do 2 constructor.
done.
Qed.

Lemma hoare_xori' : forall P Q rt rs imm, P ===> wp_xori rt rs imm Q -> 
  {{ P }} xori rt rs imm {{ Q }}.
Proof.
move=> P Q rt rs imm H.
eapply hoare_prop_m.hoare_stren; last first.
do 2 constructor.
done.
Qed.

Lemma hoare0_false  P : forall (c : cmd0), {{ FF }} c {{ P }}.
Proof.
case.
- (* nop *) apply (hoare_prop_m.hoare_stren P) => //=.
  by do 2 constructor.
- (* add *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* addi *) move=> rt rs i.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* addiu *) move=> rt rs i.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* addu *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* and *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* andi *) move=> rt rs imm.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* lw *) move=> rt off base.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* lwxs *) move=> rt idx base.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* maddu *) move=> rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* mfhi *) move=> rd.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* mflhxu *) move=> rd.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* mflo *) move=> rd.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* movn *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* movz *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* msubu *) move=> rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* mthi *) move=> rd.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* mtlo *) move=> rd.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* multu *) move=> rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* nor *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* cmd_or *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* sll *) move=> rx ry sa.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* sllv *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* sltu *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* sra *) move=> rd rt sa.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* srl *) move=> rd rt sa.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* srlv *) move=> rd rt sa.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* subu *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* sw *) move=> rt off base.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* xor *) move=> rd rs rt.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
- (* xori *) move=> rt rs imm.
  eapply hoare_prop_m.hoare_stren; last by do 2 constructor. done.
Qed.

Lemma hoare_false c P : {{ FF }} c {{ P }}.
Proof. by apply (hoare_prop_m.hoare_false' hoare0_false). Qed.

Lemma extract_exists0 : forall (c : cmd0) (A : Type) (P Q : A -> assert),
  (forall x, {{ P x }} c {{ Q x }}) ->
  {{ fun s h => exists x, P x s h }} c {{ fun s h => exists x, Q x s h }}.
Proof.
case.
- (* nop *) move=> A P Q Hc.
  apply hoare_nop' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a.
  apply H2; by do 2 constructor.
- (* add *) move=> rd rs rt A P Q Hc.
  apply hoare_add' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H).
  move/exec0_not_None_to_exec_not_None.
  move/exec0_add_not_None => H1 H2.
  split => //.
  exists a; apply H2; by do 2 constructor.
- (* addi *) move=> rt rs imm A P Q Hc.
  apply hoare_addi' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H).
  move/exec0_not_None_to_exec_not_None.
  move/exec0_addi_not_None => H1 H2.
  split => //.
  exists a; apply H2; by do 2 constructor.
- (* addiu *) move=> rt rs imm A P Q Hc.
  apply hoare_addiu' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* addu *) move=> rd rs rt A P Q Hc.
  apply hoare_addu' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* cmd_and *) move=> rd rs rt A P Q Hc.
  apply hoare_and' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* andi *) move=> rt rs imm A P Q Hc.
  apply hoare_andi' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* lw *) move=> rt off base A P Q Hc.
  apply hoare_lw' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H).
  move/exec0_not_None_to_exec_not_None.
  case/exec0_lw_not_None => p [Hp [z' Hz] ] H2.
  exists p; split => //.
  exists z'; split => //.
  exists a; apply H2; by do 2 econstructor; eauto.
- (* lwxs *) move=> rt idx base A P Q Hc.
  apply hoare_lwxs' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H).
  move/exec0_not_None_to_exec_not_None.
  case/exec0_lwxs_not_None => p [Hp [z' Hz]] H2.
  exists p; split => //.
  exists z'; split => //.
  exists a; apply H2; by do 2 econstructor; eauto.
- (* maddu *) move=> rs rt A P Q Hc.
  apply hoare_maddu' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* mfhi *) move=> rs A P Q Hc.
  apply hoare_mfhi' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* mflhxu *) move=> rd A P Q Hc.
  apply hoare_mflhxu' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* mflo *) move=> rd A P Q Hc.
  apply hoare_mflo' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* movn *) move=> rd rs rt A P Q Hc.
  apply hoare_movn' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  split => Hcondition; exists a; apply H2; by do 2 constructor.
- (* movz *) move=> rd rs rt A P Q Hc.
  apply hoare_movz' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  split => Hcondition; exists a; apply H2; by do 2 constructor.
- (* msubu *) move=> rs rt A P Q Hc.
  apply hoare_msubu' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* mthi *) move=> rs A P Q Hc.
  apply hoare_mthi' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* mtlo *) move=> rs A P Q Hc.
  apply hoare_mtlo' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* multu *) move=> rs rt A P Q Hc.
  apply hoare_multu' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* nor *) move=> rd rs rt A P Q Hc.
  apply hoare_nor' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* or *) move=> rd rs rt A P Q Hc.
  apply hoare_or' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* sll *) move=> rx ry sa A P Q Hc.
  apply hoare_sll' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* sllv *) move=> rd rs rt A P Q Hc.
  apply hoare_sllv' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* sltu *) move=> rd rt rs A P Q Hc.
  apply hoare_sltu' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* sra *) move=> rd rt sa A P Q Hc.
  apply hoare_sra' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* srl *) move=> rd rt sa A P Q Hc.
  apply hoare_srl' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* srlv *) move=> rd rt rs A P Q Hc.
  apply hoare_srlv' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* subu *) move=> rd rs rt A P Q Hc.
  apply hoare_subu' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; do 2 econstructor; eauto.
- (* sw *) move=> rt off base A P Q Hc.
  apply hoare_sw' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H).
  move/exec0_not_None_to_exec_not_None.
  case/exec0_sw_not_None => p [Hp [z' Hz] ] H2.
  exists p; split => //.
  split.
  exists z' => //.
  exists a; apply H2; do 2 econstructor; eauto.
- (* xor *) move=> rd rs rt A P Q Hc.
  apply hoare_xor' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
- (* xori *) move=> rt rs imm A P Q Hc.
  apply hoare_xori' => s h [a H].
  move/hoare_prop_m.soundness: {Hc}(Hc a).
  case/(_ s h H) => H1 H2.
  exists a; apply H2; by do 2 constructor.
Qed.

Lemma pull_out_exists : forall (A : Type) (P : A -> assert) c (Q : assert),
  (forall x, {{ P x }} c {{ Q }}) ->
  {{ fun s h => exists x, P x s h }} c {{ Q }}.
Proof.
move=> A P c Q Hc.
by apply (hoare_prop_m.pull_out_exists' extract_exists0).
Qed.

Lemma pull_out_exists_con (A : Type) (P : A -> assert) P' c Q :
  (forall x, {{ P x ** P' }} c {{ Q }}) ->
  {{ (fun s h => (exists x, P x s h)) ** P' }} c {{ Q }}.
Proof.
move=> H.
apply (hoare_prop_m.hoare_stren (fun s h => (exists x, (P x ** P') s h))).
move=> s h /= [h1 [h2 [Hdisj [Hunion [ [a H1] H2] ] ] ] ].
exists a, h1, h2 => //.
by apply pull_out_exists, H.
Qed.

Lemma pull_out_bang P Q c (A : Prop) :
  (A -> {{ P }} c {{ Q }}) ->
  {{ !(fun s => A) ** P }} c {{ Q }}.
Proof.
move=> H.
case: (Classical_Prop.classic A) => HA.
  apply (hoare_prop_m.hoare_stren P) => //.
  move=> s h /= [h1 [h2 [Hdisj [Hunion [[H1 H2] H3]]]]] //.
  subst h1.
  by rewrite Hunion heap.unioneh.
  apply H => //.
apply (hoare_prop_m.hoare_stren FF).
move=> s h /= [h1 [h2 [Hdisj [Hunion [[H1 H2] H3]]]]] //.
by apply hoare_false.
Qed.

Lemma hoare_con_comm_pre P Q c R : {{ P ** Q }} c {{ R }} -> {{ Q ** P }} c {{ R }}.
Proof. move=> H. apply (hoare_prop_m.hoare_stren (P ** Q)) => //. by apply conC. Qed.

Lemma hoare_con_assoc_pre P Q R c U : {{ P ** Q ** R }} c {{ U }} -> {{ (P ** Q) ** R }} c {{ U }}.
Proof. move=> H. apply (hoare_prop_m.hoare_stren (P ** (Q ** R))) => //. by apply conA. Qed.

(* NB: can be generalized to all instructions that suceed unconditionally *)    
Lemma cmd_and_true : forall P rd rs rt, {{ P }} cmd_and rd rs rt {{ TT }}.
Proof.
move=> P rd rs rt0.
eapply while.hoare_conseq.
by apply hoare_prop_m.entails_id.
2: by do 2 constructor.
done.
Qed.

Lemma hoare_frame_rule_and0 : forall (P Q : assert) (c : cmd0),
   hoare0 P c Q ->
   forall P' Q' : store.t -> heap.t -> Prop,
     {{P'}} c {{Q'}} ->
     {{P //\\ P'}} c {{Q //\\ Q'}}.
Proof.
move=> P Q c.
move/(while.hoare_hoare0 store.t heap.t cmd0 expr_b (fun b st => eval_b b (fst st)) hoare0 _ _ _).
move/soundness => H P' Q' H'.
apply hoare_complete.
rewrite /hoare_semantics => s h H0.
split.
  case: H0 => H01 H02.
  move: (proj1 (H s h H01)) => abs.
  contradict abs.
  constructor.
  by apply mips_cmd.semop_prop_m.exec_cmd0_inv.
move=> s' h' exec.
case: H0 => H01 H02.
move: (proj2 (H s h H01) s' h') => abs.
split.
  apply abs.
  constructor.
  by apply mips_cmd.semop_prop_m.exec_cmd0_inv.
move/soundness : H'.
rewrite /hoare_semantics.
case/(_ s h H02) => _.
apply.
done.
Qed.

Lemma exists_conC_hoare A_type P Q R c : 
  {{ fun s h => exists A, (P A ** Q) s h }} c {{ R }} ->
  {{ (fun s h => exists A : A_type, P A s h) ** Q }} c {{ R }}.
Proof.
move=> H.
eapply hoare_prop_m.hoare_stren; last by apply H.
move=> s h H' /=.
by apply exists_conC.
Qed.

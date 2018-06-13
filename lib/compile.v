(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Omega.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ssrnat_ext seq_ext.
Require while.
Require Import goto sgoto sgoto_hoare.

Module Compile (x : while.WHILE_HOARE_DETER).

Module Import sgoto_hoare_m := SGoto_Hoare x.
Import sgoto_m.
Import goto_deter_m.
Import goto_m.
Import x.

Module while_prop_m := while.While_Semop_Prop x.

(** * Compilation from %\while\ %#While# to %\sgoto%#SGoto#

   This corresponds to Section 4 of %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. *)

(** ** Compilation and Preservation/Reflection of Evaluations

   %\label{sec:compile}%

   *)

(** Figure 5 (%\figurefive%#Rules of compilation from While to SGoto#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#.
   A slight difference is that we do not remove nop instructions (they are sometimes important in MIPS assembly because
   of non-taken branch prediction).

 *)

Local Open Scope sgoto_scope.
Local Open Scope while_cmd_scope.

Import while.
Arguments ifte [cmd0 expr_b].
Arguments while [cmd0 expr_b].

Inductive compile : label -> @cmd cmd0 expr_b -> scode -> label -> Prop :=
| comp_cmd : forall l (c : cmd0), compile l c (sC l c) (S l)
| comp_seq : forall l l' l'' c d c' d',
  compile l c c' l'' -> compile l'' d d' l' -> compile l (c ; d) (c' [+] d') l'
| comp_ifte : forall l l' l'' t c d c' d',
  compile (S l'') c c' l' -> compile (S l) d d' l'' ->
  compile l (ifte t c d) (sB l (cjmp t (S l'')) [+] ((d' [+] sB l'' (jmp l')) [+] c')) l'
| comp_while : forall l l' t c prg, compile (S l) c prg l' ->
  compile l (while t c) (sB l (cjmp (neg t) (S l')) [+] (prg [+] sB l' (jmp l))) (S l').

(** Same as Figure 5 in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]# but as a function, not a predicate. *)

Fixpoint compile_f l c :=
 match c with
  | cmd_cmd0 c => sC l c
  | seq c1 c2 =>
    let c1' := compile_f l c1 in
    let c2' := compile_f (l + size (sdom c1')) c2 in
    c1' [+] c2'
  | ifte t c1 c2 =>
    let c2' := compile_f (S l) c2 in
    let c1' := compile_f (l + size (sdom c2') + 2) c1 in
    sB l (cjmp t (l + size (sdom c2') + 2)) [+]
     ((c2' [+]
       sB ((S l) + size (sdom c2')) (jmp (l + size (sdom c2') + size (sdom c1') + 2))) [+]
       c1')
  | while t c =>
   let c' := compile_f (S l) c in
     sB l (cjmp (neg t) (l + size (sdom c') + 2)) [+]
     (c' [+]
     sB ((S l) + size (sdom c')) (jmp l))
 end.

(** The above compilation-predicate and compilation-function are shown to be equivalent *)

Lemma compile_compile_f_cmd0 : forall (c : cmd0) l c' l',
  compile l c c' l' -> compile_f l c = c' /\ l' = S l.
Proof. by inversion 1. Qed.

Lemma compile_compile_f : forall c l c' l',
  compile l c c' l' -> compile_f l c = c' /\ l' = l + size (sdom c').
Proof.
elim.
- move=> c l c' l'.
  case/compile_compile_f_cmd0 => H ?; subst l'.
  split; first by exact H.
  by rewrite -H /= addnC.
- (* seq *) move=> c1 IHc1 c2 IHc2 l c' l'; inversion 1; subst.
  case/IHc1 : H3 => Hc1 Hl''.
  case/IHc2 : H6 => Hc2 Hl'.
  split.
  + by rewrite /= Hc1 -Hl'' Hc2.
  + rewrite /= size_cat; unfold label in *; ssromega.
- (* ifte *) move=> t c1 IHc1 c2 IHc2 l c' l'; inversion 1; subst.
  case/IHc1 : H6 => Hc1 Hl'.
  case/IHc2 : H7 => Hc2 Hl''.
  rewrite /= !size_cat /=.
  split; last by unfold label in *; ssromega.
  rewrite Hl'' Hc2.
  f_equal; first by repeat f_equal; unfold label in *; ssromega.
  rewrite /= -Hc1.
  f_equal; last by f_equal; unfold label in *; ssromega.
  do 3 f_equal.
  rewrite Hl' -Hc1 Hl''.
  set t1 := size (_ (compile_f _ _)).
  set t2 := size (_ (compile_f _ _)).
  rewrite (_ : t1 = t2); last by rewrite /t1 /t2; repeat f_equal; ssromega.
  ssromega.
- (* while *) move=> t c IHc l c' l'; inversion 1; subst.
  case/IHc : H5 => Hc Hl'0.
  rewrite /= size_cat /= Hl'0 Hc.
  split; last by unfold label in *; ssromega.
  repeat f_equal; unfold label in *; ssromega.
Qed.

Lemma compile_f_compile_cmd0 (c : cmd0) l c' :
  compile_f l c = c' -> compile l c c' (l + size (sdom c')).
Proof. move=> /= <- /=; rewrite addnC; by constructor. Qed.

(* Paraphrases of some constructors, not necessary but useful when used with eapply. *)

Lemma e_comp_ifte l l' l'' t c d c' d' l'_ l''_ l_ c'_ :
  compile l''_ c c' l'_ -> compile l_ d d' l'' ->
  c'_ = sB l (cjmp t (S l'')) [+] ((d' [+] sB l'' (jmp l')) [+] c') ->
  S l'' = l''_ -> l'_ = l' -> S l = l_ -> compile l (ifte t c d) c'_ l'.
Proof. move=> *; subst; by apply comp_ifte. Qed.

Lemma e_comp_while l l' t c prg c'_ l_ l'_ : compile l_ c prg l' ->
  c'_ = sB l (cjmp (neg t) (S l')) [+] (prg [+] sB l' (jmp l)) ->
  S l = l_ -> S l' = l'_ -> compile l (while t c) c'_ l'_.
Proof. move=> *; subst; by apply comp_while. Qed.

Lemma compile_f_compile : forall c l c',
  compile_f l c = c' -> compile l c c' (l + size (sdom c')).
Proof.
elim.
- exact compile_f_compile_cmd0.
- (* seq *) move=> c1 IHc1 c2 IHc2 l c' /= <-.
  eapply comp_seq; first by apply IHc1.
  rewrite /= size_cat addnA; by apply IHc2.
- (* ifte *) move=> t c1 IHc1 c2 IHc2 l c'.
  destruct c' as [ | | | c'1 c'2 ] => //.
  destruct c'2 as [ | | | c'2_1 c'2_2 ] => //.
  destruct c'2_1 as [ | | | c'2_1_1 c'2_1_2 ] => //.
  case=> Hc'1 Hc'2_1_1 H4 Hc'2_2.
  move/IHc1 : Hc'2_2 => Hc'2_2.
  case: (compile_compile_f _ _ _ _ Hc'2_2) => H6 _.
  move/IHc2 : Hc'2_1_1 => Hc'2_1_1.
  case: (compile_compile_f _ _ _ _ Hc'2_1_1) => H5 _.
  eapply e_comp_ifte.
  + by apply Hc'2_2.
  + by apply Hc'2_1_1.
  + rewrite /= -Hc'1 H5.
    f_equal; first by repeat f_equal; unfold label in *; ssromega.
    do 2 f_equal.
    rewrite -H4 /= {1}H5.
    do 2 f_equal.
    rewrite !size_cat /= {1}H5 H6; ssromega.
  + rewrite H5; ssromega.
  + rewrite /= !size_cat /= H5 -Hc'1 -H4 /=; unfold label in *; ssromega.
  + reflexivity.
- (* while *) move=> t c IHc l c'.
  destruct c' => //.
  destruct c'2 => //.
  case=> H1 /IHc H2 H3.
  case: (compile_compile_f _ _ _ _ H2) => H4 _.
  eapply e_comp_while.
  + by apply H2.
  + rewrite -H1 H4.
    f_equal; first by repeat f_equal; ssromega.
    f_equal.
    rewrite -H3 H4.
    f_equal; omega.
  + done.
  + rewrite /= !size_cat -H1 -H3 /=; ssromega.
Qed.

Lemma compile_start_label_end_label l c prg l' : compile l c prg l' -> l < l'.
Proof.
elim.
- move=> *; by auto.
- move=> l0 l'0 l'' c0 d c' d' H H0 H1 H2; ssromega.
- move=> l0 l'0 l'' _ c0 d c' d' H H0 H1 H2; ssromega.
- move=> l0 l'0 _ c0 prg' H H0; ssromega.
Qed.

(** Lemma 13 (%\lemmathirteen%#Totality and determinacy of compilation#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#:*)

Lemma totality l c : exists sc l', compile l c sc l'.
Proof. eexists. eexists. by eapply compile_f_compile; eauto. Qed.

Lemma determinacy c l l' sc : compile l c sc l' ->
  forall l'' sc', compile l c sc' l'' -> sc = sc' /\ l' = l''.
Proof.
move=> c_sc l'' sc' c_sc'.
case: (compile_compile_f _ _ _ _ c_sc) => H01 Hl'.
case: (compile_compile_f _ _ _ _ c_sc') => H11 Hl''.
by subst.
Qed.

(** Lemma 14 (%\lemmafourteen%#Domain of compiled code#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Lemma compile_sdom c l sc l' : compile l c sc l' ->
  forall p, l <= p < l' -> List.In p (sdom sc).
Proof.
elim=> /=; move=> {l l' c sc}.
- move=> l _ p H; ssromega.
- move=> l l' l'' c d c' d' Hc IHc Hd IHd p /andP [l_p p_l'].
  apply List.in_or_app.
  case : (ltnP p l'') => [p_l'' | l''_p].
  + left; apply IHc; by rewrite l_p.
  + right; apply IHd; by rewrite l''_p.
- move=> l l'0 l'' _ c0 d c' d' Hc IHc Hd IHd p.
  case/andP; rewrite leq_eqVlt; case/orP => [ /eqP -> | H1 H2 ]; first by auto.
  right.
  have [l''_p | [l''_p | p_l''] ] : l'' < p \/ l'' = p \/ p < l''.
    by case: (Nat.lt_trichotomy l'' p) => [ /ltP| [ | /ltP]]; auto.
  + apply List.in_or_app; right; apply IHc; by rewrite l''_p.
  + subst l''.
    apply List.in_or_app; left; apply List.in_or_app; right; by left.
  + apply List.in_or_app; left; apply List.in_or_app; left; apply IHd; by rewrite H1.
- move=> l l' _ c sc H IH p.
  case/andP; rewrite leq_eqVlt; move/orP => [/eqP -> | l_p]; first by auto.
  rewrite ltnS leq_eqVlt; case/orP => p_l'; right.
  + apply List.in_or_app; right => /=; by rewrite (eqP p_l'); auto.
  + apply List.in_or_app; left; apply IH; by rewrite l_p.
Qed.

Lemma compile_sdom' c l sc l' : compile l c sc l' ->
  forall p, List.In p (sdom sc) -> l <= p < l'.
Proof.
elim => {l c sc l'}.
- move=> l c p /= [H | H] //; subst; ssromega.
- move=> l l' l'' c d c' d' Hc IHc Hd IHd p /=; case/(List.in_app_or _ _ _).
  + move/IHc => H.
    apply compile_start_label_end_label in Hd; ssromega.
  + move/IHd => H.
    apply compile_start_label_end_label in Hc; ssromega.
- move=> l l' l'' t c d c' d' Hc IHc Hd IHd p /= [l_p |].
  + subst; apply compile_start_label_end_label in Hc.
    apply compile_start_label_end_label in Hd; ssromega.
  + case/(List.in_app_or _ _ _).
    * case/(List.in_app_or _ _ _) => H.
      - apply IHd in H.
        apply compile_start_label_end_label in Hc; ssromega.
      - case: H => [H |]; last by [].
        subst; apply compile_start_label_end_label in Hc.
        apply compile_start_label_end_label in Hd; ssromega.
    * move/IHc => H.
      apply compile_start_label_end_label in Hd; ssromega.
- move=> l l' t c sc Hc IHc p /= [ l_p | ].
  + subst; apply compile_start_label_end_label in Hc; ssromega.
  + case/(List.in_app_or _ _ _) => H.
    * apply IHc in H; ssromega.
    * case: H => /= [H |]; last by [].
      subst; apply compile_start_label_end_label in Hc; ssromega.
Qed.

(** Various lemmas regarding the domain of the code and labels. *)

Lemma compile_sdom_open_right sc l c l' : compile l c sc l' -> ~ List.In l' (sdom sc).
Proof. move=> H; move/(compile_sdom' _ _ _ _ H) => H'; ssromega. Qed.

Lemma compile_f_sdom_close_left : forall c sc l, compile_f l c = sc -> List.In l (sdom sc).
Proof.
elim.
+ move=> c sc l <- /=; by left.
+ move=> c1 IHc1 c2 IHc2 [] //= s s0 l [X Y]; subst.
  apply List.in_or_app; left; by apply IHc1.
+ move=> t c1 IHc1 c2 IHc2 [] //= s s0 l [X Y]; subst.
  by rewrite /=; left.
+ move=> t c IHc [] // s s0 l [X Y]; subst.
  by rewrite /=; left.
Qed.

Lemma compile_sdom_close_left l c sc l' : compile l c sc l' -> List.In l (sdom sc).
Proof.
move=> Htrans.
eapply compile_f_sdom_close_left.
case/compile_compile_f : Htrans => Htrans _.
by apply Htrans.
Qed.

Lemma compile_sdom_sS : forall c l l' c1 c2, compile l c (c1 [+] c2) l' ->
  disj (sdom c1) (sdom c2).
Proof.
case.
- move=> c l l' c1 c2; inversion 1; by subst.
- move=> c1 c2 l l' c0 c3; inversion 1; subst.
  split=> x_c0 x_c3.
  + move/(compile_sdom' _ _ _ _ H6) : x_c0 => /andP[] l_x {H6}x_l''.
    move/(compile_sdom' _ _ _ _ H7) : x_c3 => /andP[] l''_x {H7}x_l'.
    move: (leq_ltn_trans l''_x x_l''); by rewrite ltnn.
  + move/(compile_sdom' _ _ _ _ H6) : x_c3 => /andP[] l_x {H6}x_l''.
    move/(compile_sdom' _ _ _ _ H7) : x_c0 => /andP[] l''_x {H7}x_l'.
    move: (leq_ltn_trans l''_x x_l''); by rewrite ltnn.
- move=> e c1 c2 l l' c0 c3; inversion 1; subst; split=> [/=|].
  - move=> [H1 | _] //; subst.
    case/(List.in_app_or _ _ _).
    + case/(List.in_app_or _ _ _) => /=.
      * move/(compile_sdom' _ _ _ _ H8) => *; ssromega.
      * case => // H2; subst.
        apply compile_start_label_end_label in H8; ssromega.
    + move/(compile_sdom' _ _ _ _ H7) => /andP[] l''_x {H7}x_l'.
      move/compile_start_label_end_label : H8 => * /=; ssromega.
  - move=> H2 [H1 | _] //; subst.
    apply List.in_app_or in H2; case: H2.
    + case/(List.in_app_or _ _ _).
      * move/(compile_sdom' _ _ _ _ H8 _) => *; ssromega.
      * case=> // H2; subst.
        apply compile_start_label_end_label in H8; ssromega.
    + move/(compile_sdom' _ _ _ _ H7) => /andP [] {H7} l''_x x_l'.
      move/compile_start_label_end_label : H8 => * /=; ssromega.
- move=> e c l l' c1 c2; inversion 1; subst; split => /=.
  - move=> [H1 | _] //; subst.
    case/(List.in_app_or _ _ _) => /=.
    + move/(compile_sdom' _ _ _ _ H6 _) => {H6} *; ssromega.
    + case => l'0_x //; subst.
      move/compile_start_label_end_label : H6 => *; ssromega.
  - move=> H2 [H1 | _] //; subst.
    apply List.in_app_or in H2; case: H2 => /=.
    + move/(compile_sdom' _ _ _ _ H6 _) => {H6} *; ssromega.
    + case => l'0_x //; subst.
      move/compile_start_label_end_label : H6 => *; ssromega.
Qed.

(** Compilation always produces wellformed code: *)

Lemma compile_wellformed : forall c l sc l', compile l c sc l' -> wellformed sc.
Proof.
induction c.
- move=> l sc l'; inversion 1; subst; by constructor.
- move=> l sc l'; inversion 1; subst; constructor.
  + by eapply compile_sdom_sS; eauto.
  + by eapply IHc1; eauto.
  + by eapply IHc2; eauto.
- move=> l sc l'; inversion 1; subst; constructor.
  + by eapply compile_sdom_sS; eauto.
  + by constructor.
  + constructor.
    * split => /=.
      - case/(List.in_app_or _ _ _) => /= H1 x_c'.
        - case/andP: (compile_sdom' _ _ _ _ H6 _ x_c') => l''_x x_l'.
          case/andP: (compile_sdom' _ _ _ _ H7 _ H1) => K3 K4; ssromega.
        - case: H1 => // l''_x; subst.
          move: (compile_sdom' _ _ _ _ H6 _ x_c') => *; ssromega.
      - move=> H2.
        case/(List.in_app_or _ _ _) => /= [H1|].
        - case/andP: (compile_sdom' _ _ _ _ H6 _ H2) => l''_x x_l'.
          case/andP: (compile_sdom' _ _ _ _ H7 _ H1) => K3 K4; ssromega.
        - case => // l''_x; subst.
          move: (compile_sdom' _ _ _ _ H6 _ H2) => *; ssromega.
    * constructor.
      - split => /=.
        - move=> x_d' [] // H2; subst.
          move: (compile_sdom' _ _ _ _ H7 _ x_d') => *; ssromega.
        - move=> H2 x_d'.
          case: H2 => // l''_x; subst.
          move: (compile_sdom' _ _ _ _ H7 _ x_d') => *; ssromega.
      - by eapply IHc2; eauto.
      - by constructor.
    * by eapply IHc1; eauto.
- move=> l sc l'; inversion 1; subst.
  constructor.
  + by eapply compile_sdom_sS; eauto.
  + by constructor.
  + constructor.
    * split.
      - move=> x_prg [H2 | _] //; subst.
        move: (compile_sdom' _ _ _ _ H5 _ x_prg) => *; ssromega.
      - move=> [H2 | _] //; subst.
        move/(compile_sdom' _ _ _ _ H5 _) => *; ssromega.
    * by eapply IHc; eauto.
    * by constructor.
Qed.

(** Intermediate lemma for one-step instructions: *)

Lemma preservation_of_evaluations_cmd0 (c : cmd0) s s' :
  Some s -- c ---> Some s' -> forall l sc l', compile l c sc l' ->
    Some (l, s) >- sc ---> Some (l', s').
Proof.
inversion 1; subst=> n c' m; inversion 1; subst.
eapply exec_sgoto_cmd0; eauto; by constructor.
Qed.

Lemma preservation_of_evaluations_cmd0_none (c : cmd0) s :
  Some s -- c ---> None -> forall l sc l', compile l c sc l' ->
    Some (l, s) >- sc ---> None.
Proof.
inversion 1; subst => // n c' m; inversion 1; subst.
eapply exec_sgoto_cmd0; eauto; by constructor.
Qed.

Ltac apply_compile_sdom_close_left :=
  match goal with
    | H : compile ?L ?C ?SC ?K |- List.In ?L (sdom ?SC) => eapply compile_sdom_close_left; eauto
    | |- List.In ?L (sdom (sB ?L _)) => simpl; auto
  end.

Ltac decompose_In :=
  match goal with
    | |- List.In ?L (sdom (sS ?SC0 ?SC1))  => simpl; apply List.in_or_app; try decompose_In
    | |- List.In ?L (sdom (sB ?L _))       => simpl; auto
    | |- List.In ?L (cat ?D1 ?D2)          => apply List.in_or_app; try decompose_In
    | |- List.In ?L (cons ?L (@nil label)) => simpl; auto
    | |- List.In ?L ?D1 \/ List.In ?L ?D2       => solve
        [ (left; try decompose_In) | (right; try decompose_In) ]
    | |- List.In ?L (sdom ?SC)             => apply_compile_sdom_close_left
  end.

Lemma not_eq_false A (a b : A) : a <> b -> ~ (a = b \/ False).
Proof. move=> H X; by inversion_clear X. Qed.

Lemma not_eq_P A (a b : A) P : a <> b /\ ~ P -> ~ (a = b \/ P).
Proof. move=> [H1 H2] X; by inversion_clear X. Qed.

Ltac apply_compile_sdom_open_right :=
  match goal with
    | H : compile ?L ?C ?SC ?K |- ~ List.In ?K (sdom ?SC) => eapply compile_sdom_open_right; eauto
  end.

Ltac apply_compile_dom' :=
  match goal with
    | H : compile ?L ?C ?SC ?K |- ~ List.In ?M (sdom ?SC) =>
      let H1 := fresh in
        intro H1 ;
        generalize (compile_sdom' _ _ _ _ H _ H1) ; clear H ;
          let H2 := fresh in
          intro H2
  end.

Ltac apply_compile_start_label_end_label :=
  match goal with
    | H : compile ?L ?C ?SC ?K |- _ =>
      apply compile_start_label_end_label in H ;
          try apply_compile_start_label_end_label
  end.

Ltac not_in_sdom3_diff :=
  match goal with
    | |- ?L <> ?K => let H := fresh in intro H; solve [ ssromega |
        (subst L; apply_compile_start_label_end_label; ssromega) |
        (subst K; apply_compile_start_label_end_label; ssromega) ]
  end.

Ltac decompose_not_In :=
  match goal with
    | |- ~ List.In ?L (sdom (sS (sB ?L0 _) ?SC1)) =>
      simpl; apply not_eq_P; split; [ not_in_sdom3_diff | try decompose_not_In]
    | |- ~ List.In ?L (sdom (sS ?SC0 ?SC1)) =>
      simpl; apply tac_not_in_app; [ try decompose_not_In | try decompose_not_In]
    | |- ~ List.In ?L (sdom (sB ?K _)) =>
      simpl; apply not_eq_false; not_in_sdom3_diff
    | |- ~ List.In ?L (cat ?L0 ?L1) =>
      apply tac_not_in_app; [ try decompose_not_In | try decompose_not_In]
    | |- ~ List.In ?L (cons ?L0 (@nil label)) =>
      simpl; apply not_eq_false; not_in_sdom3_diff
    | |- ~ List.In ?L (sdom ?SC) =>
      solve [ apply_compile_sdom_open_right |
        (apply_compile_dom'; apply_compile_start_label_end_label; ssromega) ]
  end.

Lemma preservation_of_evaluations' c s s' : s -- c ---> s' ->
  forall n c' m, compile n c c' m -> forall st, s = Some st ->
    (forall st', s' = Some st' -> Some (n, st) >- c' ---> Some (m, st')) /\
    (s' = None -> Some (n, st) >- c' ---> None).
Proof.
elim => //; move=> {c s s'}.
- move=> c s s' H n c' m H' st X; subst; split.
  + move=> st' X; subst.
    eapply preservation_of_evaluations_cmd0; eauto; by constructor.
  + move=> X; subst.
    eapply preservation_of_evaluations_cmd0_none; eauto; by constructor.
- (* c1; c2 *) move=> s s' s'' c d Hc IHc Hd IHd n c' m H st Hs; split.
  + move=> st' Hs'.
    destruct s' as [[l' s']|].
    * inversion H; subst.
      move: {IHd}(proj1 (IHd _ _ _ H6 _ refl_equal) _ refl_equal) => IHd.
      move: {IHc}(proj1 (IHc _ _ _ H3 _ refl_equal) _ refl_equal) => IHc.
      eapply exec_sgoto_seq0; eauto; first by decompose_In.
      eapply exec_sgoto_seq1; eauto; first by decompose_In.
      apply exec_sgoto_refl; by decompose_not_In.
    * apply while_prop_m.from_none in Hd.
      by subst s''.
  + move=> Hs'.
    destruct s' as [[l' s']|].
    * inversion H; subst.
      move: {IHd}(proj2 (IHd _ _ _ H6 _ refl_equal) refl_equal) => IHd.
      move: {IHc}(proj1 (IHc _ _ _ H3 _ refl_equal) _ refl_equal) => IHc.
      eapply exec_sgoto_seq0; eauto; first by decompose_In.
      eapply exec_sgoto_seq1; eauto; first by decompose_In.
      by constructor.
    * inversion H; subst.
      apply while_prop_m.from_none in Hd.
      move: {IHc}(proj2 (IHc _ _ _ H3 _ refl_equal) refl_equal) => IHc.
      eapply exec_sgoto_seq0; eauto; first by decompose_In.
      by constructor.
- (* ifte true *) move=> s s' t c d H0 Hc IHc n c' m H st; case=> X; split.
  + move=> st' H1.
    inversion H; subst.
    apply exec_sgoto_seq0 with (Some (S l'', st)); first by decompose_In.
      apply exec_sgoto_cjmp_true => // X; subst.
      apply compile_start_label_end_label in H9; ssromega.
    apply exec_sgoto_seq1 with (Some (m, st')); first by decompose_In.
      apply exec_sgoto_seq1 with (Some (m, st')); first by decompose_In.
        by apply (proj1 (IHc _ _ _ H8 _ refl_equal)).
      apply exec_sgoto_refl; by decompose_not_In.
    apply exec_sgoto_refl; by decompose_not_In.
  + move=> H1; subst s'.
    inversion H; subst.
    apply exec_sgoto_seq0 with (Some (S l'', st)); first by decompose_In.
      apply exec_sgoto_cjmp_true => // X; subst n.
      apply compile_start_label_end_label in H8; ssromega.
    apply exec_sgoto_seq1 with None; first by decompose_In.
      apply exec_sgoto_seq1 with None; first by decompose_In.
        by apply (proj2 (IHc _ _ _ H7 _ refl_equal)).
      by constructor.
    by constructor.
- (* ifte false *) move=> s s' t c d H0 Hc IHc  n c' m H st; case=> X; split.
  + subst => st' H1.
    inversion H; subst.
    apply exec_sgoto_seq0 with (Some (S n, st)); first by decompose_In.
      by apply exec_sgoto_cjmp_false.
    apply exec_sgoto_seq1 with (Some (m, st')); first by decompose_In.
      apply exec_sgoto_seq0 with (Some (m, st')); first by decompose_In.
        apply exec_sgoto_seq0 with (Some (l'', st')); first by decompose_In.
          by apply (proj1 (IHc _ _ _ H9 _ refl_equal)).
          apply exec_sgoto_seq1 with (Some (m, st')); first by decompose_In.
            apply exec_sgoto_jmp => X; subst l''.
            apply compile_start_label_end_label in H8; ssromega.
            apply exec_sgoto_refl; by decompose_not_In.
          apply exec_sgoto_refl; by decompose_not_In.
    apply exec_sgoto_refl; by decompose_not_In.
  + subst => H1.
    inversion H; subst.
    apply exec_sgoto_seq0 with (Some (S n, st)); first by decompose_In.
      by apply exec_sgoto_cjmp_false.
    apply exec_sgoto_seq1 with None; first by decompose_In.
      apply exec_sgoto_seq0 with None; first by decompose_In.
        apply exec_sgoto_seq0 with None; first by decompose_In.
          by apply (proj2 (IHc _ _ _ H9 _ refl_equal)).
        by constructor.
      by constructor.
    by constructor.
- (* while true *) move=> s s' s'' t c H1 Hc IHc Hw IHw n c' m H st ; case=> X; subst; split.
  + move=> st' X; subst.
    destruct s' as [[l' s']|].
    * inversion H; subst.
      apply exec_sgoto_seq0 with (Some (S n, st)); first by decompose_In.
        apply exec_sgoto_cjmp_false; by rewrite eval_b_neg H1.
      apply exec_sgoto_seq1 with (Some (n, (l', s'))); first by decompose_In.
        apply exec_sgoto_seq0 with (Some (l'0, (l', s'))); first by decompose_In.
          by apply (proj1 (IHc _ _ _ H6 _ refl_equal)).
        apply exec_sgoto_seq1 with (Some (n, (l', s'))); first by decompose_In.
          apply exec_sgoto_jmp => // X; subst l'0.
          apply compile_start_label_end_label in H6; ssromega.
          eapply exec_sgoto_refl; by decompose_not_In.
      by apply (proj1 (IHw _ _ _ H _ refl_equal)).
    * by inversion Hw.
  + move=> X; subst.
    destruct s' as [[l' s']|].
    * inversion H; subst.
      apply exec_sgoto_seq0 with (Some (S n, st)); first by decompose_In.
        apply exec_sgoto_cjmp_false; by rewrite eval_b_neg H1.
      apply exec_sgoto_seq1 with (Some (n, (l', s'))); first by decompose_In.
        apply exec_sgoto_seq0 with (Some (l'0, (l', s'))); first by decompose_In.
          by apply (proj1 (IHc _ _ _ H6 _ refl_equal)).
        apply exec_sgoto_seq1 with (Some (n, (l', s'))); first by decompose_In.
          apply exec_sgoto_jmp => ?; subst l'0.
          apply compile_start_label_end_label in H6; ssromega.
          apply exec_sgoto_refl; by decompose_not_In.
      by apply (proj2 (IHw _ _ _ H _ refl_equal)).
    * inversion H; subst.
      apply exec_sgoto_seq0 with (Some (S n, st)); first by decompose_In.
        apply exec_sgoto_cjmp_false; by rewrite eval_b_neg H1.
      apply exec_sgoto_seq1 with None; first by decompose_In.
        apply exec_sgoto_seq0 with None; first by decompose_In.
          by apply (proj2 (IHc _ _ _ H6 _ refl_equal)).
        by constructor.
      by constructor.
- (* while false *) move=> s t c0 H1 n c' m1 H st; case=> X; subst; split; last by done.
  move=> st'; case=> X; subst.
  inversion H; subst.
  apply exec_sgoto_seq0 with (Some (S l', st')); first by decompose_In.
    apply exec_sgoto_cjmp_true.
    by rewrite eval_b_neg.
    move=> ?; subst; apply compile_start_label_end_label in H6; ssromega.
  apply exec_sgoto_refl; by decompose_not_In.
Qed.

(** Theorem 15 (%\theoremfifteen%#Preservation of evaluations#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Lemma preservation_of_evaluations c s l sc s' l' : compile l c sc l' ->
  Some s -- c ---> Some s' -> Some (l, s) >- sc ---> Some (l + length (sdom sc), s').
Proof.
move=> Htrans Hexec.
move: (proj1 (preservation_of_evaluations' _ _ _ Hexec _ _ _ Htrans _ refl_equal) _ refl_equal) => X.
move: (compile_compile_f _ _ _ _ Htrans) => [_ <-]; exact X.
Qed.

(** Intermediate lemmas for commands: *)

Lemma reflection_of_evaluations_sC l (c : cmd0) sc l' : compile l c sc l' ->
  forall s lstar s', Some (l, s) >- sc ---> Some (lstar, s') ->
    lstar = l' /\ (Some s -- c ---> Some s').
Proof.
inversion_clear 1=> s lstar s'; inversion_clear 1 => {sc l'}.
- inversion_clear H0.
  split; [reflexivity | by apply exec_cmd0].
- rewrite /= in H0; tauto.
Qed.

Local Open Scope goto_scope.

Lemma reflection_of_evaluations_sC_none' : forall (c : cmd0),
  forall l s, c ||- Some (l, s) ---> None -> Some s -- c ----> None.
Proof. by inversion 1. Qed.

Lemma reflection_of_evaluations_sC_none'' (c : cmd0) l s :
  Some (l, s) >- sC l c ---> None -> Some s -- c ----> None.
Proof. inversion_clear 1; by eapply reflection_of_evaluations_sC_none'; eauto. Qed.

Lemma reflection_of_evaluations_sC_none''' (c : cmd0) l s :
  Some (l, s) >- compile_f l c ---> None -> Some s -- c ----> None.
Proof. move=> /= Hexec; by eapply reflection_of_evaluations_sC_none''; apply Hexec. Qed.

Lemma reflection_of_evaluations_sC_none (c : cmd0) l s l' sc : 
  compile l c sc l' -> Some (l, s) >- sc ---> None -> Some s -- c ----> None.
Proof.
case/compile_compile_f => H1 H2 H.
rewrite -H1 in H.
by eapply reflection_of_evaluations_sC_none'''; apply H.
Qed.

(** Theorem 16 (%\theoremsixteen%#Preservation of evaluations#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu]#. *)

(** This proof is done by a nested induction to handle the while-case. We isolate this
    subcase by intermediate lemmas (one lemma for the error-free case and another lemma for the error case).
    Here follows the intermediate lemma for the error-free case; what will be the outer induction hypothesis
    in the main proof is given as an hypothesis to this intermediate lemma. *)

Lemma reflection_of_evaluations' : forall c_t
  (IHouter : forall l sc_t l' s s' lstar, compile l c_t sc_t l' -> 
    Some (l, s) >- sc_t ---> Some (lstar, s') -> 
    lstar = l' /\ Some s -- c_t ---> Some s') sc st st',
  st >- sc ---> st' ->
  forall l l' t, compile l (while t c_t) sc l' ->
    forall s lstar s' L, L = l \/ L = S l ->
      eval_b t s -> st = Some (L, s) -> st' = Some (lstar, s') ->
      lstar = l' /\ Some s -- while t c_t ---> Some s'.
Proof.
move=> c_t IHouter prg st st' H l l' t H0 s l'' s' L L_l Hneq Hst Hst'.
inversion H0; try (subst c; discriminate); subst c t0 l l'.
move: t s l'' s' L Hst Hneq Hst' l0 l'0 prg0 L_l H3 H6 H0.
induction H.
- done.
- (* exec_sgoto_cmd0 *) done.
- (* exec_sgoto_branch *) done.
- done.
- done.
- (* exec_sgoto_seq0 *) move=> t s0 l'' st' L [? ?] Hneq ? l0 l' sc' L_l [? ?] Hc_t Hwhile.
  subst sc1 sc2 l s s''.
  case: L_l => L_l; subst L.
  + (* case L = l *) apply exec_sgoto_inv_cjmp_false in H0; last by rewrite eval_b_neg Hneq; auto.
    subst s'.
    apply exec_sgoto_inv_seq1 in H1; last 2 first.
      by decompose_In.
      by decompose_not_In.
    case: H1 => [ [[l1 st1]|] [H1 H2] ].
    * apply exec_sgoto_inv_seq0 in H1; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: H1 => [ [[l2 st2]|] [H1 H3] ].
      - case/(IHouter _ _ _ _ _ _ Hc_t) : H1 => ? H1; subst l2.      
        apply exec_sgoto_inv_seq1 in H3; last 2 first. 
          by decompose_In.
          by decompose_not_In.
        case: H3 => [[ [l3 st3]|] [H3 H4] ].
        + case/(exec_sgoto_inv_jmp _ _ _ _) : H3; case=> [? ?] _; subst l3 st3.
          apply exec_sgoto_inv_refl in H4; last by decompose_not_In.
          case: H4 => X Y; subst l1 st1.
          by apply (IHexec_sgoto2 t s0 l'' st' (S l0) refl_equal Hneq refl_equal l0 l' sc'); auto.
        + by inversion H4.
      - by inversion H3.
    * by inversion H2.
  + (* case L = S l *) rewrite /= in H; inversion_clear H; last by done.
    suff : False by done. omega.
- (* exec_sgoto_seq1 *) move=> t s0 l'' st' L [? ?] Hneq Hs'' l0 l' sc' L_l [? ?] Hc_t Hwhile.
  subst sc1 sc2 l s s''.
  case: L_l => L_l; subst L.
  + (* case L = l *) have : ~ List.In l0 (sdom (sc' [+] sB l' (jmp l0))) by decompose_not_In.
    tauto. (* contradiction: l \notin sdom sc' ++ l' *)
  + (* case L = l.+1 *) clear H.
    apply exec_sgoto_inv_seq0 in H0; last 2 first.
      by decompose_In.
      by decompose_not_In.
    case: H0 => [ [[lbl0 sta0]|] [H0 H2]].
    * case/(IHouter _ _ _ _ _ _ Hc_t) : H0  => ? H0; subst lbl0.
      apply exec_sgoto_inv_seq1 in H2; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: H2 => [ [[l1 st1]|] [H2 H3] ].
      - case/(exec_sgoto_inv_jmp _ _ _ _) : H2; move=> [? ?] _; subst l1 st1.
        apply exec_sgoto_inv_refl in H3; last by decompose_not_In.
        subst s'. 
        case/boolP : (eval_b t sta0) => t_s0.
        + lapply (IHexec_sgoto2 _ sta0 l'' st' l0 refl_equal t_s0 refl_equal l0 l' sc'); auto.
          case/(_ refl_equal Hc_t Hwhile) => H2 H3.
          split => //.
          by eapply exec_while_true; eauto.
        + (* sub-tree for while is false *) apply exec_sgoto_inv_seq0 in H1; last 2 first.
            by decompose_In.
            by decompose_not_In.
          case: H1 => [ [[lout sout]|] [H1 H2] ].
          * rewrite -eval_b_neg in t_s0.
            case: {H1}(exec_sgoto_inv_cjmp_true _ _ _ _ _ H1 t_s0); case=> ? ? _; subst lout sout.
            apply exec_sgoto_inv_refl in H2; last by decompose_not_In.
            case: H2 => ? ?; subst l'' st'.
            split; first by done.
            eapply exec_while_true; eauto.
            apply exec_while_false; by rewrite -eval_b_neg.
          * by inversion H2.
      - inversion H3; subst s'.
        by inversion H1.
    * inversion H2; subst s'.
      by inversion H1.
- (* exec_sgoto_refl *) move=> t s0 l'' st' L [? ?] Hneq [? ?] l0 l' sc' L_l Hsc H9 H0.
  subst L s l'' st'; rewrite -Hsc /= in H.
  case: L_l => L_l.
  + subst l; rewrite /= in H; tauto.
  + have X : List.In (S l0) (sdom sc' ++ (l' :: nil)).
      apply compile_sdom_close_left in H9.
      apply List.in_or_app.
      tauto.
    subst l; rewrite /= in H; tauto.
Qed.

Lemma reflection_of_evaluations'' : forall c_t
  (IHouter : forall l sc l', compile l c_t sc l' -> forall s, 
    (forall lstar s', Some (l, s) >- sc ---> Some (lstar, s') ->
      lstar = l' /\ Some s -- c_t ---> Some s') /\
    (Some (l, s) >- sc ---> None -> Some s -- c_t ---> None)) sc st st',
  st >- sc ---> st' ->
  forall l l' t, compile l (while t c_t) sc l' ->
    forall s L, L = l \/ L = S l ->
      eval_b t s -> st = Some (L, s) -> st' = None ->
      Some s -- while t c_t ---> None.
Proof.
move=> d IndHyp sc ST ST' H l l' t H1 s0 L H2 Hneq H3 H4.
inversion H1; try (subst c; discriminate); subst c t0 l l'.
move: t s0 L H3 Hneq H4 l0 l'0 prg H2 H6 H9 H1.
induction H.
- done.
- (* exec_sgoto_cmd0 *) done.
- (* exec_sgoto_branch *) done.
- done.
- done.
- (* exec_sgoto_seq0 *) move=> t s0 L [? ?] Hneq Hs'' l0 l' sc' L_l [? ?] Hsc' Hwhile.
  subst sc1 sc2 l s s''.
  case: L_l => L_l; subst L.
  + (* case L = l *) apply exec_sgoto_inv_cjmp_false in H0; last by rewrite eval_b_neg Hneq; auto.
    subst s'.
    apply exec_sgoto_inv_seq1 in H1; last 2 first.
      by decompose_In.
      by decompose_not_In.
    case: H1 => [ [[l1 st1]|] [H1 H2] ].
    * apply exec_sgoto_inv_seq0 in H1; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: H1 => [ [[l2 st2]|] [H1 H3] ].
      - case/(proj1 (IndHyp _ _ _ Hsc' _) _ _) : H1 => ? H1; subst l2.      
        apply exec_sgoto_inv_seq1 in H3; last 2 first.
          by decompose_In.
          by decompose_not_In.
        case: H3 => [ [[l3 st3]|] [H3 H4] ].
        + case/(exec_sgoto_inv_jmp _ _ _ _) : H3; case=> ? ? _; subst l3 st3.
          apply exec_sgoto_inv_refl in H4; last by decompose_not_In.
          case: H4 => ? ?; subst l1 st1.
          by move: (IHexec_sgoto2 _ s0 (S l0) refl_equal Hneq refl_equal l0 l' sc'); auto.
        + by inversion H4.
      - by inversion H3.
    * apply exec_sgoto_inv_seq0 in H1; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: H1 => [ [[l2 st2]|] [H1 H3] ].
      - case/(proj1 (IndHyp _ _ _ Hsc' _) _ _) : H1 => ? H1; subst l2.      
        apply exec_sgoto_inv_seq1 in H3; last 2 first.
          by decompose_In.
          by decompose_not_In.
        case: H3 => [ [[l3 st3]|] [H3 H4] ].
        + case/(exec_sgoto_inv_jmp _ _ _ _) : H3; case=> ? ? _; subst l3 st3.
          apply exec_sgoto_inv_refl in H4; [done | by decompose_not_In].
        + by inversion H3.
      - move/(proj2 (IndHyp _ _ _ Hsc' _)) : H1 => H1.
        eapply exec_while_true; eauto.
        by constructor.
  + (* case L = S l *) rewrite /= in H; inversion_clear H; last by done.
    suff : False by done. omega.
- (* exec_sgoto_seq1 *) move=> t s0 L [? ?] Hneq Hs'' l0 l' sc' L_l [? ?] Hsc' Hwhile.
  subst sc1 sc2 l s s''.
  case: L_l => ?; subst L.
  + (* cae L = l *) have : ~ List.In l0 (sdom (sc' [+] sB l' (jmp l0))) by decompose_not_In.
    tauto. (* contradiction: l \notin sdom sc' ++ l' *)
  + (* case L = l.+1 *) clear H.
    apply exec_sgoto_inv_seq0 in H0; last 2 first.
      by decompose_In.
      by decompose_not_In.
    case: H0 => [ [[lbl0 sta0]|] [H0 H2] ].
    * case/(proj1 (IndHyp _ _ _ Hsc' _) _ _) : H0 => ? H0; subst lbl0.      
      apply exec_sgoto_inv_seq1 in H2; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: H2 => [ [[l1 st1]|] [H2 H3] ].
      - case/(exec_sgoto_inv_jmp _ _ _ _) : H2; case=> ? ? _; subst l1 st1.
        apply exec_sgoto_inv_refl in H3; last by decompose_not_In.
        subst s'.
        case/boolP : (eval_b t sta0) => t_s0.
        + lapply (IHexec_sgoto2 _ sta0 l0 refl_equal t_s0 refl_equal l0 l' sc'); auto.
          move=> H5.
          eapply exec_while_true => //.
          by apply H0.
          by apply H5.
        + (* sub-tree for while is false *) apply exec_sgoto_inv_seq0 in H1; last 2 first.
            by decompose_In.
            by decompose_not_In.
          case: H1 => [ [ [lout sout]|] [H1 H2] ].
          * rewrite -eval_b_neg in t_s0.
            case: {H1}(exec_sgoto_inv_cjmp_true _ _ _ _ _ H1 t_s0); case=> ? ? _; subst lout sout.
            apply exec_sgoto_inv_refl in H2; [done | by decompose_not_In].
          * by inversion H1.
      - inversion H3; subst s'.
        by inversion H2.
    * inversion H2; subst s'.
      eapply exec_while_true => //.
      by apply (proj2 (IndHyp _ _ _ Hsc' _) H0).
      by constructor.
- done.
Qed.

Lemma reflection_of_evaluations : forall c l sc l', compile l c sc l' ->
  forall s, (forall lstar s',
    Some (l, s) >- sc ---> Some (lstar, s') -> lstar = l' /\ Some s -- c ---> Some s') /\
  (Some (l, s) >- sc ---> None -> Some s -- c ---> None).
Proof.
elim.
- (* cmd_cmd0 *) move=> c l sc l' Hcomp s; split.
  + move=> lstar s' Hexec; by eapply reflection_of_evaluations_sC; eauto.
  + move=> Hexec; apply exec_cmd0.
    by eapply reflection_of_evaluations_sC_none; eauto.
- (* seq *) move=> c1 IHc1 c2 IHc2 l sc lstar Hcomp s.
  inversion_clear Hcomp as [| ? l' l''_ c d sc1 sc2 Hcomp_c1 Hcomp_c2 Hl0l Hcc1 Hsc1sc2sc Hl'lstar | |].
  split.
  + move=> lstar0 s' Hexec_sc.
    apply exec_sgoto_inv_seq0 in Hexec_sc; last 2 first.
      by decompose_In.
      by decompose_not_In.
    case: Hexec_sc => [ [[l'' s'']|] [Hexec_sc1 Hexec_sc''] ].
    * case: {IHc1}(proj1 (IHc1 _ _ _ Hcomp_c1 s) _ _ Hexec_sc1) => Hl''l''_ Hexec_c1; subst l''_.
      apply exec_sgoto_inv_seq1 in Hexec_sc''; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: Hexec_sc'' => [ [[l3 s3]|] [Hexec_sc2 Hexec_sc3] ].
      - case: {IHc2}(proj1 (IHc2 _ _ _ Hcomp_c2 s'') _ _ Hexec_sc2) => ? Hexec_c2; subst l3.
        apply exec_sgoto_inv_refl in Hexec_sc3; last by decompose_not_In.
        case: Hexec_sc3 => Hlstarlstar0 Hs3s'; subst lstar0 s3.
        split; [reflexivity | by apply exec_seq with (Some s'')].
      - by inversion Hexec_sc3.
    * by inversion Hexec_sc''.
  + move=> Hexec_sc.
    apply exec_sgoto_inv_seq0 in Hexec_sc; last 2 first.
      by decompose_In.
      by decompose_not_In.
    case: Hexec_sc => [ [[l'' s'']|] [Hexec_sc1 Hexec_sc''] ].
    * case: {IHc1}((proj1 (IHc1 _ _ _ Hcomp_c1 s)) _ _ Hexec_sc1) => X Hexec_c1; subst l''_.
      apply exec_sgoto_inv_seq1 in Hexec_sc''; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: Hexec_sc'' => [ [[l3 s''']|] [Hexec_sc2 Hexec_sc3] ].
      - case: {IHc2}(proj1 (IHc2 _ _ _ Hcomp_c2 s'') _ _ Hexec_sc2) => ? Hexec_c2; subst l3.
        apply exec_sgoto_inv_refl in Hexec_sc3; [done | by decompose_not_In].
      - move: {IHc2}(proj2 (IHc2 _ _ _ Hcomp_c2 s'') Hexec_sc2) => Hexec_c2.
        by eapply exec_seq; eauto.
    * move: {IHc1}((proj2 (IHc1 _ _ _ Hcomp_c1 s)) Hexec_sc1) => Hexec_c1.
      by eapply exec_seq; eauto||econstructor.
- (* ifte *) move=> t c_t IHc_t c_f IHc_f l sc l' Hcomp s.
  inversion Hcomp as [| | l0 l'0 l'' t0 c d sc_t sc_f Hcomp_c_t Hcomp_c_f Hl0l Ht0t Hsc Hl'0l |]; subst.
  split.
  - (* no error *) move=> lstar s' Hexec_sc.
    apply exec_sgoto_inv_seq0 in Hexec_sc; last 2 first.
      by decompose_In.
      by decompose_not_In.
    case: Hexec_sc => [ [[l3 s3]|] [Hexec_cjmp Hexec_sc3] ]; last by inversion Hexec_sc3.
    case/boolP : (eval_b t s) => Hbtest.
    + (* test true *) case: {Hexec_cjmp}(exec_sgoto_inv_cjmp_true _ _ _ _ _ Hexec_cjmp Hbtest) => Hexec_cjmp _ //.
      case: Hexec_cjmp => X Y; subst.
      move/(proj2 (sem_equ_ass _ _ _ (wellformed_ass' _ _ _ (compile_wellformed _ _ _ _ Hcomp)) _ _ )) : Hexec_sc3 => Hexec_sc3.
      apply exec_sgoto_inv_seq1 in Hexec_sc3; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: Hexec_sc3 => [ [[l4 s4]|] [Hexec_sc_t4 Hexec_sc4] ]; last by inversion Hexec_sc4.
      move/(proj1 (sem_equ_ass _ _ _ (wellformed_ass' _ _ _ (compile_wellformed _ _ _ _ Hcomp)) _ _ )) : Hexec_sc4 => Hexec_sc4.
      case: {IHc_t}(proj1 (IHc_t _ _ _ Hcomp_c_t _) _ _ Hexec_sc_t4) => X Hexec_c_t; subst l4.
      apply exec_sgoto_inv_refl in Hexec_sc4; last by decompose_not_In.
      case: Hexec_sc4 => X Y; subst lstar s4.
      split; first by reflexivity.
      by eapply exec_ifte_true; eauto.
    + (* test false *) apply exec_sgoto_inv_cjmp_false in Hexec_cjmp; last by done.
      case: Hexec_cjmp => X Y; subst.
      apply exec_sgoto_inv_seq1 in Hexec_sc3; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: Hexec_sc3 => [ [ [l3 s3]|] [Hexec_jump_sc_t3 Hexec_sc3] ]; last by inversion Hexec_sc3.
      apply exec_sgoto_inv_seq0 in Hexec_jump_sc_t3; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: Hexec_jump_sc_t3 => [ [[l4 s4]|] [Hexec_sc_f_jmp4 Hexec_sc_f_jmp_sc_t4] ]; last by inversion Hexec_sc_f_jmp_sc_t4.
      apply exec_sgoto_inv_seq0 in Hexec_sc_f_jmp4; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: Hexec_sc_f_jmp4 => [ [[l5 s5]|] [Hexec_sc_f5 Hexec_sc_f_jmp5] ]; last by inversion Hexec_sc_f_jmp5.
      case: {IHc_f}((proj1 (IHc_f _ _ _ Hcomp_c_f _)) _ _ Hexec_sc_f5) => X Hexec_c_f; subst l5.
      apply exec_sgoto_inv_seq1 in Hexec_sc_f_jmp5; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: Hexec_sc_f_jmp5 => [ [ [l6 s6]|] [Hexec_jmp6 Hexec_sc_f_jmp6] ]; last by inversion Hexec_sc_f_jmp6.
      case: {Hexec_jmp6}(exec_sgoto_inv_jmp _ _ _ _ Hexec_jmp6); case => ? ? _; subst l6 s6.
      apply exec_sgoto_inv_refl in Hexec_sc_f_jmp6; last by decompose_not_In.
      case: Hexec_sc_f_jmp6 => X Y; subst l4 s4.
      apply exec_sgoto_inv_refl in Hexec_sc_f_jmp_sc_t4; last by decompose_not_In.
      case: Hexec_sc_f_jmp_sc_t4 => X Y; subst l3 s3.
      apply exec_sgoto_inv_refl in Hexec_sc3; last by decompose_not_In.
      case: Hexec_sc3 => ? ?; subst lstar s5.
      split; first by reflexivity.
      by apply exec_ifte_false.
  - (* error case *) move=> Hexec_sc.
    apply exec_sgoto_inv_seq0 in Hexec_sc; last 2 first.
      by decompose_In.
      by decompose_not_In.
    case: Hexec_sc => [ [[l3 s3]|] [Hexec_cjmp Hexec_sc3] ]; last by inversion Hexec_cjmp.
    case/boolP : (eval_b t s) => Hbtest.
    + (* test true *) case: {Hexec_cjmp}(exec_sgoto_inv_cjmp_true _ _ _ _ _ Hexec_cjmp Hbtest); case=> X Y // _; subst l3 s3.
      apply exec_sgoto_inv_seq1 in Hexec_sc3; last 2 first.
        by decompose_In.
        by decompose_not_In.
      case: Hexec_sc3 => [ [[l4 s4]|] [Hexec_sc_t4 Hexec_sc4]].
      * apply exec_sgoto_inv_seq1 in Hexec_sc_t4; last 2 first.
          by decompose_In.
          by decompose_not_In.
        case: Hexec_sc_t4 => [ [ [l5 s5]|] [Hexec_sc_t5 Hexec_sc5] ]; last by inversion Hexec_sc5.
        case: {IHc_t}((proj1 (IHc_t _ _ _ Hcomp_c_t s)) _ _ Hexec_sc_t5) => X Hexec_ct5; subst l5.
        apply exec_sgoto_inv_refl in Hexec_sc5; last by decompose_not_In.
        case: Hexec_sc5 => X Y; subst l4 s5.
        apply exec_sgoto_inv_refl in Hexec_sc4; [done | by decompose_not_In].
      * apply exec_sgoto_inv_seq1 in Hexec_sc_t4; last 2 first.
          by decompose_In.
          by decompose_not_In.
        case: Hexec_sc_t4 => [ [[l5 s5]|] [Hexec_sc_t5 Hexec_sc5] ].
        - case: {IHc_t}((proj1 (IHc_t _ _ _ Hcomp_c_t s)) _ _ Hexec_sc_t5) => X Hexec_ct5; subst l5.
          apply exec_sgoto_inv_refl in Hexec_sc5; [done | by decompose_not_In].
        - move: {IHc_t}(proj2 (IHc_t _ _ _ Hcomp_c_t s) Hexec_sc_t5) => Hexec_c_t5.
          by eapply exec_ifte_true; eauto.
    + (* test false *) apply exec_sgoto_inv_cjmp_false in Hexec_cjmp.
      * case: Hexec_cjmp => X Y; subst l3 s3.
        apply exec_sgoto_inv_seq1 in Hexec_sc3; last 2 first.
          by decompose_In.
          by decompose_not_In.
        case: Hexec_sc3 => [ [[l4 s4]|] [Hexec_sc_t4 Hexec_sc4] ].
        - apply exec_sgoto_inv_seq0 in Hexec_sc_t4; last 2 first.
            by decompose_In.
            by decompose_not_In.
          case: Hexec_sc_t4 => [ [[l5 s5]|] [Hexec_sc_t5 Hexec_sc5] ]; last by inversion Hexec_sc5.
          apply exec_sgoto_inv_seq0 in Hexec_sc_t5; last 2 first.
            by decompose_In.
            by decompose_not_In.
          case: Hexec_sc_t5 => [ [[l6 s6]|] [Hexec_sc_t6 Hexec_sc6] ]; last by inversion Hexec_sc6.
          case: {IHc_f}(proj1 (IHc_f _ _ _ Hcomp_c_f s) _ _ Hexec_sc_t6) => ? Hexec_ct6; subst l6.
          apply exec_sgoto_inv_seq1 in Hexec_sc6; last 2 first.
            by decompose_In.
            by decompose_not_In.
          case: Hexec_sc6 => [ [[l7 s7]|] [Hexec_sc_t7 Hexec_sc7] ]; last by inversion Hexec_sc7.
          case/(exec_sgoto_inv_jmp _ _ _ _) : Hexec_sc_t7; case=> ? ? _; subst l7 s7.
          apply exec_sgoto_inv_refl in Hexec_sc7; last by decompose_not_In.
          case: Hexec_sc7 => X Y; subst l5 s5.
          apply exec_sgoto_inv_refl in Hexec_sc5; last by decompose_not_In.
          case: Hexec_sc5 => X Y; subst l4 s4.
          apply exec_sgoto_inv_refl in Hexec_sc4; [done | by decompose_not_In].
        - apply exec_sgoto_inv_seq0 in Hexec_sc_t4; last 2 first.
            by decompose_In.
            by decompose_not_In.
          case: Hexec_sc_t4 => [ [ [l5 s5]|] [Hexec_sc_t5 Hexec_sc5] ].
          + apply exec_sgoto_inv_seq0 in Hexec_sc_t5; last 2 first.
              by decompose_In.
              by decompose_not_In.
            case: Hexec_sc_t5 => [ [[l6 s6]|] [Hexec_sc_t6 Hexec_sc6] ]; last by inversion Hexec_sc6.
            case: {IHc_f}(proj1 (IHc_f _ _ _ Hcomp_c_f s) _ _ Hexec_sc_t6) => ? Hexec_ct6; subst l6.
            apply exec_sgoto_inv_seq1 in Hexec_sc6; last 2 first.
              by decompose_In.
              by decompose_not_In.
            case: Hexec_sc6 => [ [ [l7 s7]|] [Hexec_sc_t7 Hexec_sc7] ]; last by inversion Hexec_sc7.
            case/(exec_sgoto_inv_jmp _ _ _ _) : Hexec_sc_t7; case=> ? ? _; subst l7 s7.
            apply exec_sgoto_inv_refl in Hexec_sc7; last by decompose_not_In.
            case: Hexec_sc7 => X Y; subst l5 s5.
            apply exec_sgoto_inv_refl in Hexec_sc5; [done | by decompose_not_In].
          + apply exec_sgoto_inv_seq0 in Hexec_sc_t5; last 2 first.
              by decompose_In.
              by decompose_not_In.
            case: Hexec_sc_t5 => [ [[l6 s6]|] [Hexec_sc_t6 Hexec_sc6] ].
            * case: {IHc_f}((proj1 (IHc_f _ _ _ Hcomp_c_f s)) _ _ Hexec_sc_t6) => X Hexec_ct6; subst l6.
              apply exec_sgoto_inv_seq1 in Hexec_sc6; last 2 first.
                by decompose_In.
                by decompose_not_In.
              case: Hexec_sc6 => [ [ [l7 s7]|] [Hexec_sc_t7 Hexec_sc7] ]; last by inversion Hexec_sc_t7.
              case/(exec_sgoto_inv_jmp _ _ _ _) : Hexec_sc_t7; case=> ? ? _; subst l7 s7.
              apply exec_sgoto_inv_refl in Hexec_sc7; [done | by decompose_not_In].
            * apply exec_ifte_false => //.
              exact: (proj2 (IHc_f _ _ _ Hcomp_c_f s) Hexec_sc_t6).
      * done.
- (* while case *) move=> t c_t IHouter l sc l' Hcomp s.
  inversion Hcomp as [| | | l0 l'_ t0 c prg Hc_tprg Hl0l Ht0t0 Hsc HSl0'l']; subst.
  split.
  + (* no error *) move=> lstar s' Hexec_sc.
    apply exec_sgoto_inv_seq0 in Hexec_sc; last 2 first.
      by decompose_In.
      by decompose_not_In.
    case: Hexec_sc => [ [[l_ s_]|] [Hexec_beq Hexec_sc] ]; last by inversion Hexec_sc.
    case/boolP : (eval_b (neg t) s) => Heq.
    * case: {Hexec_beq}(exec_sgoto_inv_cjmp_true _ _ _ _ _ Hexec_beq Heq); case=> ? ? _; subst l_ s_.
      apply exec_sgoto_inv_refl in Hexec_sc; last by decompose_not_In.
      case: Hexec_sc => X Y; subst lstar s'.
      split; first by reflexivity.
      apply exec_while_false => //.
      by rewrite eval_b_neg in Heq.
    * have IndHyp: forall n c' n' st st' m, compile n c_t c' n' ->
        Some (n, st) >- c' ---> Some (m, st') -> m = n' /\ (Some st -- c_t ---> Some st').
        move=> n c' n' st st' m H H0.
        move/IHouter : H => H.
        exact: (proj1 (H _) _ _ H0).
      apply (reflection_of_evaluations' _ IndHyp _ _ _ Hexec_sc _ _ _ Hcomp _ _ _ (S l)) => //.
      - by auto.
      - rewrite eval_b_neg in Heq; by move/negPn : Heq.
      - by apply exec_sgoto_inv_cjmp_false in Hexec_beq.
  + (* error *) move=> Hexec_sc.
    apply exec_sgoto_inv_seq0 in Hexec_sc; last 2 first.
      by decompose_In.
      by decompose_not_In.
    case: Hexec_sc => [ [ [l_ s_]|] [Hexec_beq Hexec_sc] ]; last by inversion Hexec_beq.
    case/boolP : (eval_b (neg t) s) => Heq.
    * case: {Hexec_beq}(exec_sgoto_inv_cjmp_true _ _ _ _ _ Hexec_beq Heq); case=> ? ? // _; subst l_ s_.
      apply exec_sgoto_inv_refl in Hexec_sc; [done | by decompose_not_In].
    * have IndHyp : forall n c' n' st, compile n c_t c' n' -> 
        Some (n, st) >- c' ---> None -> (Some st -- c_t ---> None).
        move=> n c' n' st H H0.
        exact: (proj2 (IHouter _ _ _ H st) H0).
      apply exec_sgoto_inv_cjmp_false in Hexec_beq => //.
      case: Hexec_beq => X Y; subst l_ s_.
      apply: (reflection_of_evaluations'' _ IHouter _ _ _ Hexec_sc _ _ _ Hcomp _ (S l)) => //.
      - by auto.
      - rewrite eval_b_neg in Heq; by move/negPn : Heq.
Qed.

(** ** Preservation/Reflection of Derivable Hoare Triples

   % \label{thm:hoare-triple-preservation} %

   Theorem 17 (%\theoremseventeen%#Preservation of derivable Hoare triples#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu]#. 
   The proof of this theorem makes use of the soundness of Hoare logic for %\while%#While#;
   this is the lemma %\coqdocvar{soundness}%#soundness# used below.

   *)

Local Open Scope while_hoare_scope.
Local Open Scope sgoto_hoare_scope.

Module while_hoare_prop_m := While_Hoare_Prop x.

Lemma preservation_hoare P Q c : {{ P }} c {{ Q }} ->
  forall l sc l', compile l c sc l' ->
    [^ fun pc => fun s h => pc = l /\ P s h ^] sc [^ fun pc => fun s h => pc = l' /\ Q s h ^].
Proof.
move=> Hoare l sc l' Hcompile.
apply hoare_sgoto_complete; first by eapply compile_wellformed; eauto.
move=> l0 s h [-> HP] {l0}.
move/while_hoare_prop_m.soundness: Hoare.
case/(_ _ _ HP) => Herror_free HQ.
move/reflection_of_evaluations: Hcompile.
case/(_ (s, h)) => Hcompile1 Hcompile2.
split.
- by move=> X; apply Hcompile2 in X.
- move=> l'_ s' h' Hexec.
  case/Hcompile1 : Hexec => l'_l'.
  by move/HQ.
Qed.

(** Theorem 18 (%\theoremeighteen%#Reflection of derivable Hoare triples#). The proof of this theorem uses in
   particular the completeness of Hoare-logic for %\while%#While#. *)

Lemma reflection_hoare l c sc l' : compile l c sc l' ->
  forall P Q, [^ P ^] sc [^ Q ^] -> {{ P l }} c {{ Q l' }}.
Proof.
move=> Hcompile P Q.
move/hoare_sgoto_sound => Hoare_semantics.
apply while_hoare_prop_m.hoare_complete => s h.
case/Hoare_semantics => Herror_free HQ.
split.
- contradict Herror_free.
  by apply (proj2 (preservation_of_evaluations' _ _ _ Herror_free _ _ _ Hcompile _ refl_equal) refl_equal).
- move=> s' h'.
  move/(preservation_of_evaluations _ _ _ _ _ _ Hcompile) => Hexec.
  move/HQ : {HQ} Hexec => HQ.
  by case/compile_compile_f : Hcompile => _ ->.
Qed.

(**
   #
   Bibliography:
   [Saabas&Uustalu] Ando Saabas and Tarmo Uustalu. A compositional natural semantics and Hoare logic for low-level languages. Theor. Comput. Sci. 373(3): 273-302, Elsevier 2007.

   [Affeldt&Marti] Reynald Affeldt and Nicolas Marti. An Approach to Formal Verification of Arithmetic Functions in Assembly. ASIAN 2006. LNCS 4435, pp. 346-360, Springer 2008.
   #

   *)

End Compile.

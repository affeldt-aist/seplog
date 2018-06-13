(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Omega.
From mathcomp Require Import ssreflect ssrbool.
Require while.
Require Import goto sgoto.

(** * Hoare Logic of %\sgoto%#SGoto#
   
   %\label{sec:sgoto_hoare}%

   This corresponds to Section 3.2 of %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. 
   The type %\coqdockw{assert}%#assert# was defined in 
   %Section \ref{sec:while}%#the module for the While language#.
*)

Module SGoto_Hoare (while_hoare_deter_m : while.WHILE_HOARE_DETER).

Module Import sgoto_m := SGoto while_hoare_deter_m.
Import goto_deter_m.
Import goto_m.
Import while_hoare_deter_m.

(** printing //\\ %\ensuremath{\land}%*)

Definition assn := label -> assert.

Local Open Scope while_assert_scope.

Definition restrict (P : assn) d : assn := fun l => P l //\\ (fun _ _ => List.In l d).

Definition restrict_cplt (P : assn) d : assn := fun l => while.Not (fun _ _ => List.In l d) //\\ P l.

Lemma restrict_dom : forall l d (P : assn) s h, List.In l d -> P l s h -> restrict P d l s h.
Proof. done. Qed.

Lemma restrict_cplt_dom : forall (P : assn) l s h d, P l s h -> ~ List.In l d -> restrict_cplt P d l s h. 
Proof. done. Qed.

Reserved Notation "'[^' P '^]' c '[^' Q '^]'" (at level 82, no associativity).

(** printing ===> %\ensuremath{\Longrightarrow}%*)

(** Figure 3 (%\figurethree%#Hoare rules of SGoto#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#.
   %\coqdocvar{wp0} is explained in Section \ref{sec:while}.% 
   %$\Longrightarrow$ used in the rule \coqdocvar{hoare\_sgoto\_conseq} is the entailment for \coqdockw{assert}.% *)

Local Open Scope sgoto_scope.

Notation "'_assn'" := assn : sgoto_hoare_scope. (* dummy *)
Local Open Scope sgoto_hoare_scope.

Inductive hoare_sgoto : assn -> scode -> assn -> Prop :=
| hoare_cmd : forall l c P,
  [^ fun pc => fun s h => pc = l /\ (wp0 c (P (S l))) s h \/ pc <> l /\ P pc s h ^] 
     sC l c [^ P ^]
| hoare_jmp : forall l j Q,
  [^ fun pc => fun s h => pc = l /\ (Q j s h \/ j = l) \/ pc <> l /\ Q pc s h ^] 
     sB l (jmp j) [^ Q ^] 
| hoare_branch : forall l b j Q,
  [^ fun pc => fun s h => 
     pc = l /\ (~~ eval_b b (s, h) /\ Q (S l) s h \/ eval_b b (s, h) /\ ( Q j s h \/ j = l)) \/
     pc <> l /\ Q pc s h ^] 
     sB l (cjmp b j) [^ Q ^] 
| hoare_sO : forall P, [^ P ^] sO [^ P ^]
| hoare_sS : forall sc0 sc1 P,
  [^ restrict P (sdom sc0) ^] sc0 [^ P ^] -> [^ restrict P (sdom sc1) ^] sc1 [^ P ^] -> 
  [^ P ^] sc0 [+] sc1 [^ restrict_cplt P (sdom (sc0 [+] sc1)) ^]
| hoare_sgoto_conseq : forall sc (P Q P' Q': assn),
  (forall l, P l ===> P' l) -> (forall l, Q' l ===> Q l) ->
  [^ P' ^] sc [^ Q' ^] -> [^ P ^] sc [^ Q ^]
where "'[^' P '^]' c '[^' Q '^]'" := (hoare_sgoto P c Q) : sgoto_hoare_scope.

(** Theorem 10 (%\theoremten%#Soundness#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Module while_semop_prop_m := while.While_Semop_Prop while_hoare_deter_m.

Lemma hoare_sgoto_sound : forall sc P Q, [^ P ^] sc [^ Q ^] ->
  forall l s h, P l s h -> ~ (Some (l, (s, h)) >- sc ---> None) /\
    forall l' s'  h', Some (l, (s, h)) >- sc ---> Some (l', (s', h')) -> Q l' s' h'.
Proof.
move=> sc Pi Pi'; elim=> //=; clear sc Pi Pi'.
- move=> l c Pi l0 s0 h0 [ [l0_l X2] | [l0_l X2] ]; split.
  + subst l0 => X.
    inversion X; subst.
    inversion H3; subst.
    by move: (wp0_no_err _ _ _ _ X2).
  + move=> l' s' h' Hexec; subst l0.
    case/(exec_sgoto_inv_cmd _ _ _ _ _) : Hexec => X; subst.
    move/while_semop_prop_m.exec_cmd0_inv => Hexec.
    by eapply exec0_wp0; [apply Hexec | exact X2].
  + move=> X; inversion X; by subst.
  + move=> l' s'  h'.
    move/(exec_sgoto_inv_refl _ _ _ _) => H.
    have : ~ List.In l0 (sdom (sC l c)) by rewrite /=; intuition.
    by case/H => ? ?; subst => <-.
- move=> l j Q l0 s0 h0 [ [l0_l [X2 | X2] ] | [l0_l X2] ]; split.
  + by move=> X; inversion X.
  + move=> l' s' h' Hexec; subst l.
    by case/(exec_sgoto_inv_jmp _ _ _ _) : Hexec; case=> ? ? ? _; subst.
  + by move=> X; inversion X.
  + move=> l' s' h' Hexec; subst.
    inversion Hexec; subst => //.
    rewrite /= in H1; tauto.
  + by move=> X; inversion X.
  + move=> l' s' h' Hexec.
    apply exec_sgoto_inv_refl in Hexec.
    * case: Hexec => K1 K2 K3; by subst.
    * rewrite /=; contradict l0_l; by case: l0_l.
- move=> l b j Q l0 s0 h0 [[l0_l [ [X3 HQ] | [X2 [X3|j_l] ] ] ] | [l0_l HQ] ]; split.
  + by move=> X; inversion X.
  + move=> l' s' h' Hexec; subst l.
    by case: {Hexec}(exec_sgoto_inv_cjmp_false _ _ _ _ _ Hexec X3) => ? ? ?; subst.
  + by move=> X; inversion X.
  + move=> l' s' h' Hexec; subst l.
    case: {Hexec}(exec_sgoto_inv_cjmp_true _ _ _ _ _ Hexec X2); case => X Y Z _; by subst.
  + by move=> X; inversion X.
  + move=> l' s' h' Hexec; subst.
    inversion Hexec; subst => //.
    by rewrite X2 in H0.
    rewrite /= in H1; tauto.
  + by move=> X; inversion X.
  + move=> l' s' h'  Hexec.
    move: (exec_sgoto_inv_refl _ _ _ _ Hexec) => H.
    have : ~ List.In l0 (sdom (sB l (cjmp b j))) by rewrite /=; intuition.
    case/H=> K1 K2 K3; by subst.
- move=> Pi l0 s0 h0 HPil0; split.
  + by move=> X; inversion X.
  + move=> l' s' h'.
    move/(exec_sgoto_inv_refl _ _ _ _) => /= X.
    have : ~ False by tauto.
    case/X => Y Z V; by subst.
- move=> sc1 sc2 P Hsc0 IHsc0 Hsc1 IHsc1 l0 s0 h0 HP_l0; split.
  + move Hst0 : (Some (l0, (s0, h0))) => st0.
    move Hst' : None => st'.
    move Hsc : (sc1 [+] sc2) => sc.
    move=> Hexec.
    move: Hexec sc1 sc2 P Hsc0 IHsc0 Hsc1 IHsc1 Hsc l0 s0 h0 HP_l0 Hst0 Hst'.
    elim => //; move=> {sc st0 st'}.
    + move=> sc1 sc2 l0 st0 s' s'' HInl0sc1 Hexec_sc1 _(*IHsc1*) Hsc IHsc sc1' sc2' Pi. 
      move=> Hressc1 IHsc1' Hressc2 IHsc2 Hsc'; subst.
      case: Hsc' => X Y; subst sc1' sc2'.
      move=> l0' s0 h0 HPi_l0 [? ?]; subst.
      move=> Y; subst s''.
      move: (restrict_dom _ _ _ _ _ HInl0sc1 HPi_l0) => X.
      destruct s' as [ [l' [s' h'] ] | ].
      - move: (proj2 (IHsc1' _ _ _ X) _ _ _ Hexec_sc1).
        move/(IHsc _ _ _ Hressc1 IHsc1' Hressc2 IHsc2 (refl_equal _) _ _ _); tauto.
      - move: {IHsc1'}(proj1 (IHsc1' _ _ _ X)); tauto.
    + move=> sc1 sc2 l0 st0 s' s'' HInl0sc2 Hexec_sc2 _(*IHsc2*) Hexec_sc IHsc sc1' sc2' Pi. 
      move=> Hressc1 IHsc1' Hressc2 IHsc2 Hsc'; subst.
      case: Hsc' => X Y; subst sc1' sc2'.
      move=> l0' s0 h0 HPi_l0 [? ?]; subst.
      destruct s' as [ [ l' [s' h'] ] | ].
      - move=> Y; subst s''.
        move: (restrict_dom _ _ _ _ _ HInl0sc2 HPi_l0) => X.
        move: (proj2 (IHsc2 _ _ _ X) _ _ _ Hexec_sc2).
        move/(IHsc _ _ _ Hressc1 IHsc1' Hressc2 IHsc2 (refl_equal _) _ _ _); tauto.
      - move: (restrict_dom _ _ _ _ _ HInl0sc2 HPi_l0) => X.
        move: {IHsc2}(proj1 (IHsc2 _ _ _ X)); tauto.
  + move=> l' s' h' Hexec .
    move Hst0 : (Some (l0, (s0, h0))) => st0.
    move Hst' : (Some (l', (s', h'))) => st'.
    move Hsc : (sc1[+]sc2) => sc.
    rewrite Hst0 Hst' Hsc in Hexec.
    move: Hexec sc1 sc2 P Hsc0 IHsc0 Hsc1 IHsc1 Hsc l0 s0 h0 l' s' h' HP_l0 Hst0 Hst'.
    elim => //; move=> {sc st0 st'}.
    + move=> sc1 sc2 l0 st0 s' s'' HInl0sc1 Hexec_sc1 _(*IHsc1*) Hsc IHsc sc1' sc2' Pi. 
      move=> Hressc1 IHsc1' Hressc2 IHsc2 Hsc'; subst.
      case: Hsc' => X Y; subst sc1' sc2'.
      move=> l0' s0 h0 l'_ s'0 h' HPi_l0 [? ?]; subst => Y.
      move: (restrict_dom _ _ _ _ _ HInl0sc1 HPi_l0) => X.
      destruct s'' as [ [l'' [s'' h'']] | ] => //.
      case: Y => ? ? ?; subst.
      destruct s' as [ [l' [s' h']] | ].
      - move: ((proj2 (IHsc1' _ _ _ X)) _ _ _ Hexec_sc1) => H.
        by move: {IHsc1' IHsc2 IHsc} (IHsc _ _ _ Hressc1 IHsc1' Hressc2 IHsc2 (refl_equal _) _ _ _ _ _ _  H (refl_equal _) (refl_equal _)).
      - by inversion Hsc.
    + move=> sc1 sc2 l0 st0 s' s'' HInl0sc2 Hexec_sc2 _(*IHsc2*) Hexec_sc IHsc sc1' sc2' Pi. 
      move=> Hressc1 IHsc1' Hressc2 IHsc2 Hsc'; subst.
      case: Hsc' => X Y; subst sc1' sc2'.
      move=> l0' s0 h0 l'_ s'_ h'_ HPi_l0 [? ?]; subst.
      destruct s' as [ [l' [s' h']] | ].
      - destruct s'' as [ [l'' [s'' h'']] | ] => //.
        case=> ? ? ?; subst.
        move: (restrict_dom _ _ _ _ _ HInl0sc2 HPi_l0) => X.
        move: (proj2 (IHsc2 _ _ _ X) _ _ _ Hexec_sc2) => H.
        by move: {IHsc1' IHsc2 IHsc} (IHsc _ _ _ Hressc1 IHsc1' Hressc2 IHsc2 (refl_equal _) _ _ _ _ _ _ H (refl_equal _) (refl_equal _)).
      - by inversion Hexec_sc.
    + move=> sc l st HnotInlsc sc1 sc2 Pi Hressc1 IHsc1 Hressc2 IHsc2 Hsc l0 s0 h0 l' s' h' HP_l0 [? ?]; subst.
      case=> ? ? ?; by subst.
- move=> sc P Q P' Q' HP HQ Hsc IH l0 s0 h0 HP_l0; split.
  + move=> X.
    move: (HP _ _ _ HP_l0) => H2.
    by move: (proj1 (IH _ _ _ H2) X).
  + move=> l' s' h' Hexec .
    move: (HP _ _ _ HP_l0) => H2.
    move: (proj2 (IH _ _ _ H2) _ _ _ Hexec) => H4.
    by apply HQ.
Qed.

(** The semantic definition of the weakest precondition from %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#.
   The additional conjunct is to take errors into account.
*)

Definition wlp_semantics (sc : scode) (Pi : assn) : assn := fun l s h =>
  ~ (Some (l, (s, h)) >- sc ---> None) /\
  forall l' s' h', Some (l, (s, h)) >- sc ---> Some (l', (s', h')) -> Pi l' s' h'.

(** Lemma 11 in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Lemma wlp_completeness : forall sc (Hwf : wellformed sc) Q, [^ wlp_semantics sc Q ^] sc [^ Q ^].
Proof.
elim .
- move=> Hwf Q.
  apply hoare_sgoto_conseq with (P':=wlp_semantics sO Q) (Q':=wlp_semantics sO Q); last by apply hoare_sO.
  + by move=> *.
  + move=> l s0 h0 Hwlp; by apply (proj2 Hwlp), exec_sgoto_refl.
- move=> l c Hwf Q.
  apply hoare_sgoto_conseq with (P':= fun pc s h =>
    pc = l /\ (wp0 c (Q (S l))) s h \/
    pc <> l /\ Q pc s h) (Q' := Q); last by apply hoare_cmd.
  + move=> l0 s0 h0 Hwlp.
    have [l0_l | l_l0] : l0 = l \/ l <> l0 by unfold label; omega.
    * left; subst; split => //.
      rewrite /wlp_semantics in Hwlp.
      case: (cmd0_terminate c (s0, h0)) => s' Hs'.
      destruct s' as [[s h]|].
      - eapply exec0_wp0; [by apply Hs' | idtac].
        apply (proj2 Hwlp).
        eapply exec_sgoto_cmd0; eauto.
        by constructor.
      - case: Hwlp => H H0.
        have : Some (l, (s0, h0)) >- sC l c ---> None by do 2 constructor.
        contradiction.
    * right; split; auto.
      rewrite /wlp_semantics in Hwlp.
      apply (proj2 Hwlp), exec_sgoto_refl => /=; tauto.
  + by rewrite /while.entails.
- move=> l [].
  + (* jmp *) move=> j Hwf Q.
    apply hoare_sgoto_conseq with (P' := fun pc s h =>
        pc = l /\ (Q j s h \/ j = l) \/
        pc <> l /\ Q pc s h) (Q' := Q); last by apply hoare_jmp.
    * move=> l0 s0 h0 Hwlp.
      have [l0_l | l_l0] : l0 = l \/ l <> l0 by unfold label; omega.
      - subst; left; split => //.
        rewrite /wlp_semantics in Hwlp.
        have [j_l | j_l] : j = l \/ j <> l by unfold label; omega.
        + by subst; auto.
        + left; apply (proj2 Hwlp).
          by eapply exec_sgoto_jmp; eauto.
      - right; split; auto.
        rewrite /wlp_semantics in Hwlp.
        apply (proj2 Hwlp), exec_sgoto_refl => /=; tauto.
    * by rewrite /while.entails.
  + (* cjmp *) move=> t j Hwf Q.
    apply hoare_sgoto_conseq with (P':= fun pc s h => pc = l /\
        (~~ eval_b t (s, h) /\ Q (S l) s h \/
          eval_b t (s, h) /\ ( Q j s h \/ j = l)) \/
        pc <> l /\ Q pc s h) (Q' := Q); last by apply hoare_branch.
    + move=> l0 s0 h0 Hwlp.
      have [l0_l | l_l0] : l0 = l \/ l <> l0 by unfold label; omega.
      * subst; left; split => //.
        case/boolP : (eval_b t (s0, h0)) => Heval.
        - right; split => //.
          have [j_l | j_l] : j = l \/ j <> l by unfold label; omega.
          - subst; by right.
          - left; apply (proj2 Hwlp).
            by eapply exec_sgoto_cjmp_true; eauto.
        - left; split; first by done.
          rewrite /wlp_semantics in Hwlp.
          apply (proj2 Hwlp).
          by eapply exec_sgoto_cjmp_false; eauto.
      * right; split; first by auto.
        apply (proj2 Hwlp), exec_sgoto_refl => /=; tauto.
    + by rewrite /while.entails.   
- move=> sc0 IHsc0 sc2 IHsc1 Hwf Q.
  apply hoare_sgoto_conseq with (P' := wlp_semantics (sc0 [+] sc2) Q) 
    (Q' := restrict_cplt (wlp_semantics (sc0 [+] sc2) Q) (sdom (sc0 [+] sc2))).
  + by rewrite /while.entails.
  + move=> l s h.
    rewrite /restrict_cplt /wlp_semantics; case=> Hres1 Hres2.
    by apply (proj2 Hres2), exec_sgoto_refl.
  + apply hoare_sS.
    * apply hoare_sgoto_conseq with (P' := wlp_semantics sc0 (wlp_semantics (sc0 [+] sc2) Q)) 
      (Q' := wlp_semantics (sc0 [+] sc2) Q).
      - move=> l s h.
        rewrite /restrict /while.And; case=> H2 l_sc0; split.
        + rewrite /wlp_semantics in H2.
          case: H2 => H H0.
          contradict H.
          eapply exec_sgoto_seq0; eauto.
          by constructor.
        + move=> l' s' h' Hsc0; split.
          * rewrite /wlp_semantics in H2.
            case: H2 => H H0.
            contradict H.
            by eapply exec_sgoto_seq0; eauto.
          * move=> l'' s'' h'' Hsc.
            apply (proj2 H2).
            by eapply exec_sgoto_seq0; eauto.
      - by rewrite /while.entails.
      - apply IHsc0.
        by eapply wellformed_inv_L; eauto.
    * apply hoare_sgoto_conseq with (P' := wlp_semantics sc2 (wlp_semantics (sc0 [+] sc2) Q)) 
      (Q' := wlp_semantics (sc0 [+] sc2) Q).
      - move=> l s h.
        rewrite /restrict /while.And; case=> H2 l_sc2; split.
        + rewrite /wlp_semantics in H2.
          case : H2 => H H0.
          contradict H.
          eapply exec_sgoto_seq1; eauto.
          by constructor.
        + move=> l' s' h' Hsc2; split.
          * rewrite /wlp_semantics in H2.
            case: H2 => H H0.
            contradict H.
            by eapply exec_sgoto_seq1; eauto.
          * move=> l'' s'' h'' Hsc.
            apply (proj2 H2).
            by eapply exec_sgoto_seq1; eauto.
      - by rewrite /while.entails.
      - apply IHsc1.
        by eapply wellformed_inv_R; eauto.
Qed.

(** Theorem 12 (%\theoremtwelve%#Completeness#) in %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#. *)

Lemma hoare_sgoto_complete : forall (P Q : assn) sc (Hwf : wellformed sc),
  (forall l s h, P l s h ->
    ~  Some (l, (s, h)) >- sc ---> None  /\
    (forall l' s' h', Some (l,(s,h)) >- sc ---> Some (l',(s',h')) -> Q l' s' h')) ->
  [^ P ^] sc [^ Q ^].
Proof.
move=> P Q sc Hwf Hsemax.
apply hoare_sgoto_conseq with (P' := wlp_semantics sc Q) (Q' := Q).
- move=> l s h HP.
  rewrite /wlp_semantics; split.
  + by apply (proj1 (Hsemax _ _ _ HP)).
  + move=> l' s' h' Hexec.
    by apply (proj2 (Hsemax _ _ _ HP)).
- by rewrite /while.entails.
- by apply wlp_completeness.
Qed.

End SGoto_Hoare.


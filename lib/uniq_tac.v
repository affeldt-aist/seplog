(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Permutation.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import seq_ext.

Declare Scope uniq_scope.

Reserved Notation "'uniq(' a , .. , b ')'" (at level 10,
  no associativity, format "'[v' 'uniq(' a , .. , b ')' ']'").

Section uniq_ext.

Variable A : eqType.

Lemma uniq_NoDup : forall (l : seq A), uniq l -> List.NoDup l.
Proof.
elim => [| hd tl IH /=]; first by constructor.
case/andP; move/negP => H1 H2.
constructor; last by apply IH.
contradict H1.
by apply/inP.
Qed.

Lemma NoDup_uniq : forall (l : seq A), List.NoDup l -> uniq l.
Proof.
elim => // hd tl IH /=; inversion_clear 1; apply/andP; split; last by apply IH.
apply/negP; contradict H0; by apply/inP.
Qed.

Lemma uniq_head (hd : A) tl tl' : ~ List.In hd tl' ->
  (uniq tl -> uniq tl') -> uniq (hd :: tl) -> uniq (hd :: tl').
Proof.
move=> Hhd Htl /=; case/andP=> H1 H2; apply/andP; split; last by auto.
apply/negP; contradict Hhd; by apply/inP.
Qed.

Lemma uniq_head' (hd : A) tl (lst' : seq A) :
  (uniq tl -> uniq lst') -> uniq (hd :: tl) -> uniq lst'.
Proof. move=> Htl /=. case/andP=> H1 H2. by apply Htl. Qed.

Lemma uniq_rotate : forall t (h : A), uniq (h :: t) -> uniq (t ++ h :: nil).
Proof.
elim=> // hd' tl IH hd /=; case/andP; rewrite negb_or; case/andP => H1 H4.
case/andP => H2 H3; apply/andP; split.
- apply/negP; move/inP.
  case/(@List.in_app_or A) => [H | /= H].
  + by move/inP : H2.
  + case : H => // H; by rewrite H eqxx in H1.
- apply IH; by apply/andP.
Qed.

Lemma uniq_rotate' (hd : A) tl (lst' : seq A) :
  (uniq (tl ++ hd :: nil) -> uniq lst') -> uniq (hd :: tl) -> uniq lst'.
Proof. move=> Htl Hlst; apply Htl; by apply uniq_rotate. Qed.

Lemma uniq_head1 (hd : A) tl : uniq (hd :: tl) -> uniq tl.
Proof. move=> /=. by case/andP. Qed.

Lemma list_is_not_set_hd_hd (hd : A) tl : uniq (hd :: hd :: tl) -> False.
Proof. by rewrite /= !inE !eqxx. Qed.

Lemma Permutation_uniq (l1 l2 : seq A) : Permutation l1 l2 -> uniq l1 -> uniq l2.
Proof.
elim => //; clear l1 l2.
- move=> x l l' H IH /=; case/andP; move/negP => H1 H2.
  apply/andP; split; last by apply IH.
  apply/negP.
  contradict H1.
  move/inP : H1 => H1.
  apply/inP.
  apply Permutation_sym in H.
  by eapply Permutation_in; eauto.
- move=> x y l; rewrite [(x :: l)]lock [(y ::l)]lock /= -!lock.
  case/andP; move/negP => H1 H2; rewrite /= in H1 H2.
  apply/andP; split=> [| /=].
  + apply/negP; contradict H1; rewrite /= in H1; case/orP : H1.
    * move/eqP => ->; by rewrite in_cons eqxx.
    * case/andP : H2; move/negP => ? _; tauto.
  + apply/andP; split.
    * move/negP : H1; apply: contra => yl; by rewrite in_cons yl orbC.
    * by case/andP : H2.
- move=> l l' l'' Hll' IH1 Hl'l'' IH2 Hl; by apply IH2, IH1.
Qed.

Lemma uniq_rotate'' : forall hd (tl : A), uniq (hd ++ tl :: nil) -> uniq (tl :: hd).
Proof.
elim => // hd tl IH tl'.
rewrite -cat1s -catA.
apply Permutation_uniq, Permutation_sym.
rewrite -cat1s catA.
by apply permut_rotate.
Qed.

Lemma uniq_cat_inv : forall (l k : seq A), uniq (l ++ k) -> uniq l /\ uniq k.
Proof.
elim=> // h t IH k /=; case/andP; move/negP.
move/negP/inP => H1 H2.
split; last by apply IH in H2; tauto.
apply/andP; split; last by apply IH in H2; tauto.
apply/negP.
move/inP.
contradict H1.
apply List.in_or_app; by auto.
Qed.

Lemma disj_uniq : forall (l k : seq A),
  uniq l -> uniq k -> disj l k -> uniq (l ++ k).
Proof.
elim=> // hd tl IHl k Hhdtl Hk Hinter /=; apply/andP; split; first last.
  apply IHl => //.
  by eapply uniq_head1; eauto.
  by eapply disj_cons_inv; eauto.
rewrite /= in Hhdtl; case/andP : Hhdtl => Hhdtl1 Hhdtl2.
rewrite mem_cat negb_or Hhdtl1 /=.
apply: contra Hhdtl1 => /inP Hhdtl1.
move/(@disj_not_In _ _ hd) : Hinter => /(_ Hhdtl1) /=.
tauto.
Qed.

Lemma uniq_disj : forall (l k : seq A), uniq (l ++ k) -> disj l k.
Proof.
elim=> [| hd tl IH k /= ]; first by move=> k _; apply disj_nil_L.
case/andP. move/negP. move/negP/inP => H1 H2.
apply disj_sym, disj_cons_R.
- exact/disj_sym/IH.
- contradict H1; apply List.in_or_app; by auto.
Qed.

Lemma substitution_uniq : forall n s, size s = n ->
  Permutation s (iota O n) ->
  forall (def : A) l k, size l = n -> size k = n ->
    (forall i, (i < n)%nat -> nth def k i = nth def l (nth 0 s i)) ->
    uniq l -> uniq k.
Proof.
move=> n s Hlens Hperm def l k Hlenl Hlenk H.
apply Permutation_uniq, Permutation_sym.
by eapply substitution_Permutation; eauto.
Qed.

End uniq_ext.

Arguments uniq_rotate'' [A].
Arguments uniq_cat_inv [A].

Notation "'uniq(' a , .. , b ')'" := (uniq (cons a .. (cons b nil) ..)) : uniq_scope.

Ltac remove_useless :=
  match goal with
    | |- is_true (uniq ?l) -> is_true (uniq ?k)=>
      let inj := compute_list_injection l k in
      let perm := eval compute in
          (remove_idx l (fun x => negb (x \in inj(*inb EqNat.beq_nat x inj*))) O) in
      let Htmp := fresh in
      move=> Htmp ;
      move: (uniq_remove_idx Htmp (fun x => negb (x \in inj (*inb EqNat.beq_nat x inj*))) O);
      rewrite [remove_idx _ _ _]/= {Htmp}
  end.

Goal forall {T : eqType} (a b c : T), uniq [:: b; c; a] -> uniq [:: a; b].
move=> T a b c.
remove_useless.
Abort.

Ltac loop n :=
  match n with
    | O => idtac
    | S ?m => (case => //) ; loop m
  end.

Ltac loop' n :=
  match n with
    | O => idtac
    | S ?m => (move/Lt.lt_S_n) ; loop' m
  end.

Ltac uniq_permut default_value :=
  match goal with
    | |- is_true (uniq ?l) -> is_true (uniq ?k)=>
      let bij := compute_list_injection l k in
      let len := eval compute in (size l) in
      let Hn := fresh in
      let Hnot_lt_O := fresh in
        apply substitution_uniq with
          (n:=len) (s:=bij) (def:=default_value);
          [done | apply (@function_permut_Permutation _ Peano_dec.eq_nat_dec len) => // | done | done |
            (
              loop len ; move=> Hn ; loop' len ;
              move: (Lt.lt_n_O Hn) => Hnot_lt_O; move/Hnot_lt_O => //
            )
          ]
  end.

Ltac Uniq_uniq default_value :=
   match goal with
   | H:is_true (uniq ?l1) |- is_true (uniq ?l2) =>
     move: H; remove_useless ; uniq_permut default_value
   end.

(* INPUT: a list
   OUTPUT: returne Some element if this element appears at least twice in the list,
	   None o.w. *)
Ltac look_for_double_in_list lst :=
  match lst with
    | nil => None
    | (?hd :: ?tl) =>
      match In_list hd tl with
        | true => constr:(Some hd)
        | false => look_for_double_in_list tl
      end
  end.

(* INPUT: a context with (uniq lst) and a candidate element
   SIDE-EFFECT: remove all elements except the candidate, eliminate the goal if this is a double *)
Ltac uniq_remove_elements candidate :=
  match goal with
    | H:is_true (uniq (candidate :: candidate :: _)) |- _ =>
      move: {H}(list_is_not_set_hd_hd _ _ _ H) => //
    | H:is_true (uniq (candidate :: ?tl)) |- _ =>
      move: {H}(uniq_rotate _ _ _ H); simpl cat; move=> H ;
        uniq_remove_elements candidate
    | H:is_true (uniq (?hd :: ?tl)) |- _ =>
      move: {H}(uniq_head1 _ _ _ H) => H ;
        uniq_remove_elements candidate
    | _ => fail "no interesting uniq predicate in the context"
  end.

(* INPUT: a context with (uniq lst) and a False goal
   SIDE-EFFECT: eliminate the goal if the list is not a set *)

(*Ltac uniq_false :=
  let candidate :=
    match goal with
      | H:is_true (uniq ?lst) |- False => look_for_double_in_list lst
    end
  in
  match candidate with
    | Some ?candidate' => uniq_remove_elements candidate'
    | _ => fail "no double in the uniq predicate"
  end.*)

(* NB: change 2011/4/04 the code has been changed so that
the tactic tries all the "uniq" hypotheses in the context
in turn; this improvement was necessary to cope with the
situation arising in begcd where there are one context for
seplog vars and one context for regs *)
Ltac uniq_false :=
    match goal with
      | H:is_true (uniq ?lst) |- False =>
        let candidate := look_for_double_in_list lst in

  match candidate with
    | Some ?candidate' => uniq_remove_elements candidate'
    | _ => clear H; uniq_false
(*    | _ => fail "no double in the uniq predicate"*)
  end

      | _ => fail "no double in any uniq predicate"
    end.

Ltac Uniq_not_In_singleton := match goal with
| [ H : is_true (uniq ?lst) |- ~ List.In ?a (?k :: nil) ] =>
  let K := fresh in
    move=> /= [K | // ];
      match k with
        | _ => rewrite <- K in H
      end ;
      uniq_false
end.

Ltac Uniq_not_In :=
  match goal with
    | [ H : is_true (uniq ?lst) |- ~ List.In ?a (?b :: nil) ] =>
      by Uniq_not_In_singleton
    | [ H : is_true (uniq ?lst) |- ~ List.In ?a (?b :: ?k) ] =>
      apply tac_not_In_cons; [by Uniq_not_In_singleton | Uniq_not_In]
    | |- ?X => idtac X
  end.

Ltac Uniq_neq :=
  match goal with
    | [ H : is_true (uniq ?lst) |- ?a <> ?b ] =>
      let K := fresh in
        intro K;
        rewrite <- K in H
        ;
          uniq_false
  end.

Ltac Disj_uniq def :=
  match goal with
  | |- disj (_ :: _) (_ :: _) =>
    Disj_remove_dup ;
    apply uniq_disj; rewrite [cat _ _]/=; by Uniq_uniq def
  end.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
Require Import Init_ext ssrZ ZArith_ext String_ext ssrnat_ext seq_ext.
Require Import machine_int.
Import MachineInt.

Require Import littleop.
Require Import C_types C_types_fp.
Require Import C_value.
Require Import C_expr C_expr_equiv C_expr_ground.
Require Import C_seplog.
Require Import C_contrib.

Local Open Scope nat_scope.
Local Open Scope seq_scope.

Arguments Z.of_nat n : simpl never.

Module C_Tactics_f (C_Env : CENV).

Definition g := C_Env.g.
Definition sigma := C_Env.sigma.

Module Import C_contrib_m := C_Contrib_f C_Env.
Export C_contrib_m.

Local Open Scope C_types_scope.

Definition icon (l : seq assert) := nosimpl Sum con assert_abelean l.

Lemma iconE l : icon l = Sum con l.
Proof. done. Qed.

Instance icon_morphism_equiv : Morphisms.Proper (permutation ==> equiv) icon.
move => l1 l2 Hl; rewrite /icon; by apply/Sum_morphism.
Qed.

Instance icon_morphism_entails : Morphisms.Proper (permutation ==> entails) icon.
move => l1 l2 Hl; rewrite /icon; by rewrite -> (Sum_morphism _ _ Hl).
Qed.

Notation "'icon(' a , .. , b ')'" := (icon (cons a .. (cons b nil) ..)) (at level 10, no associativity, format "'[v' 'icon(' a , .. , b ')' ']'") : C_assert_scope.

Lemma icon_cons : forall t (h : assert), icon (h :: t) ===> h ** icon t.
Proof. elim => // h. by rewrite /icon /= conPe. reflexivity. Qed.

Lemma cons_icon : forall t (h : assert), h ** icon t ===> icon (h :: t).
Proof. elim => // h. by rewrite /icon /= conPe. reflexivity. Qed.

Lemma monotony_L_con_icon (t : seq assert) t' (h : assert) :
  t' ===> icon t -> h ** t' ===> icon (h :: t).
Proof.
move=> H; apply (ent_trans (h ** icon t)); by [apply monotony_L | apply cons_icon].
Qed.

Lemma monotony_L_icon_con (t : seq assert) t' (h : assert) :
  icon t ===> t' -> icon (h :: t) ===> h ** t'.
Proof.
move=> H. apply (ent_trans (h ** icon t)); by [apply icon_cons | apply monotony_L].
Qed.

Local Open Scope nat_scope.

(* conversion between assert goal to icon representation *)

Ltac Sum_sem_compute :=
  match goal with
    | |- Sum_sem _ (?P ** ?Q) => eapply op_sem; [Sum_sem_compute | Sum_sem_compute]
    | |- Sum_sem _ emp => eapply zero_sem
    | |- Sum_sem _ _ => eapply elt_sem
  end.

Goal (@Sum_sem _ (fun a b => a ** b) assert_abelean ((emp :: nil) ++ (emp :: nil)) (emp ** emp)).
by apply op_sem; apply elt_sem.
Abort.

Ltac Rewrite_to_icon P :=
  let iconP := fresh in
  evar (iconP : seq assert);
  let iconP_P := fresh in
  (have iconP_P : @Sum_sem _ _ assert_abelean iconP P by unfold iconP; Sum_sem_compute);
  rewrite -(Sum_sem_conv iconP_P); unfold iconP; clear iconP iconP_P; rewrite -iconE /=.

Goal forall P Q R, (P ** Q) ** R ===> icon(P,Q).
move=> P Q R.
match goal with
|- ?P ===> ?Q => Rewrite_to_icon P
end.
Abort.

Ltac assert_to_seq' P :=
  match P with
    | (?P1 ** ?P2) =>
      let p1 := assert_to_seq' P1 in
      let p2 := assert_to_seq' P2 in
      constr: (p1 ++ p2)
    | emp => constr:(@Nil assert)
    | _ => constr: (P :: nil)
  end.

Ltac assert_to_seq P :=
  let Ps := assert_to_seq' P in eval simpl in Ps.

Ltac seq_to_assert P :=
  match P with
    | cons ?hd ?tl =>
      let tl' := seq_to_assert tl in constr: (hd ** tl')
    | cons ?hd nil => hd
  end.

Lemma ent_L_coneP Q P : Q ===> P -> emp ** Q ===> P.
Proof. move=> *; by rewrite coneP. Qed.

Lemma ent_L_conPe Q P : Q ===> P -> Q ** emp ===> P.
Proof. move=> *; by rewrite conPe. Qed.

Lemma ent_R_coneP Q P : Q ===> P -> Q ===> emp ** P.
Proof. move=> *; by rewrite coneP. Qed.

Lemma ent_R_conPe Q P : Q ===> P -> Q ===> P ** emp.
Proof. move=> *; by rewrite conPe. Qed.

Ltac Ent_L_flat_match_gen tac :=
match goal with
| |- (?Q1 ** ?Q2) ** ?Q3 ===> ?Q =>
  refine (ent_trans (Q1 ** Q2 ** Q3) ((Q1 ** Q2) ** Q3) Q (equiv_imp2 _ _ (conA Q1 Q2 Q3)) _) ;
  Ent_L_flat_match_gen tac
| |- emp ** ?Q2 ===> _ => apply ent_L_coneP; Ent_L_flat_match_gen tac
| |- ?Q2 ** emp ===> _ => apply ent_L_conPe; Ent_L_flat_match_gen tac
| |- ?Q1 ** ?Q2 ===> _ => tac; Ent_L_flat_match_gen tac
| |- _ ===> _ => idtac
end.

Ltac Ent_L_flat_match_icon_tac := apply monotony_L_con_icon.

Ltac Ent_L_flat_match_icon := Ent_L_flat_match_gen Ent_L_flat_match_icon_tac.

Goal forall P Q R S T U V W X Y Z,
  P ** (Q ** R ** S) ** (T ** U) ** V ** W ** X ** Y ** Z ===>
  icon (P :: Q :: R :: S :: T :: U :: V :: W :: X :: Y :: Z :: nil).
intros.
Ent_L_flat_match_icon.
Abort.

Ltac Ent_L_flat_match_tac :=  apply monotony_L.

Ltac Ent_L_flat_match := Ent_L_flat_match_gen Ent_L_flat_match_tac.

Goal forall P Q R S T U V W X Y Z,
  P ** (Q ** R ** S) ** (T ** U) ** V ** W ** X ** Y ** Z ===>
  P ** Q ** R ** S ** T ** U ** V ** W ** X ** Y ** Z.
Proof.
intros.
Ent_L_flat_match.
Abort.

Ltac Ent_R_flat_match_gen tac :=
match goal with
| |- ?Q ===> (?Q1 ** ?Q2) ** ?Q3 =>
  refine (ent_trans (Q1 ** Q2 ** Q3) Q ((Q1 ** Q2) ** Q3) _ (equiv_imp _ _ (conA Q1 Q2 Q3))) ;
  Ent_R_flat_match_gen tac
| |- _ ===> emp ** ?Q2 => apply ent_R_coneP; Ent_R_flat_match_gen tac
| |- _ ===> ?Q2 ** emp => apply ent_R_conPe; Ent_R_flat_match_gen tac
| |- _ ===> ?Q1 ** ?Q2 => tac; Ent_R_flat_match_gen tac
| |- _ ===> _ => idtac
end.

Ltac Ent_R_flat_match_icon_tac := apply monotony_L_icon_con.

Ltac Ent_R_flat_match_icon := Ent_R_flat_match_gen Ent_R_flat_match_icon_tac.

Ltac Ent_R_flat_match := Ent_R_flat_match_gen Ent_L_flat_match_tac.

Ltac Ent_L_flat :=
  match goal with
    | |- ?P ===> ?Q =>
      eapply ent_trans; [ Ent_L_flat_match; apply ent_id | idtac ]
  end.

Ltac Ent_L_to_icon :=
  match goal with
    | |- ?P ===> ?Q =>
      let Ps := assert_to_seq P in
      refine (ent_trans (icon Ps) P Q _ _) ;
      first by Ent_L_flat_match_icon
  end.

Goal forall P Q R S T U V W X Y Z,
  P ** (Q ** R ** S) ** T ** U ** V ** W ** X ** Y ** Z ===> FF.
move => *.
Ent_L_flat.
Ent_L_to_icon.
Abort.

Ltac Ent_R_flat :=
  match goal with
    | |- ?P ===> ?Q =>
      eapply ent_trans; [ idtac | Ent_R_flat_match; apply ent_id ]
  end.

Ltac Ent_R_to_icon :=
  match goal with
    | |- ?P ===> ?Q =>
      let Qs := assert_to_seq Q in
      refine (ent_trans (icon Qs) P Q _ _);
      last by Ent_R_flat_match_icon
    | |- _ <==> ?Q => Rewrite_to_icon Q
  end.

Goal forall P Q R S, FF ===> (P ** Q) ** (R ** S).
move => *.
Ent_R_flat.
Ent_R_to_icon.
Abort.

Ltac Ent_LR_to_icon :=
  match goal with
    | |- _ ===> _ => Ent_L_to_icon ; Ent_R_to_icon
  end.

Goal forall P Q R S, P ** Q ** R ** S ===> FF.
move => *.
Ent_LR_to_icon.
Abort.

Ltac Hoare_L_to_icon :=
  match goal with
    | |- {{ ?P }} _ {{ _ }} =>
      let Ps := assert_to_seq P in
      apply (hoare_stren (icon Ps));
      first by Ent_L_flat_match_icon
  end.

Ltac Hoare_R_to_icon :=
  match goal with
    | |- {{ _ }} _ {{ ?P }} =>
      let Ps := assert_to_seq P in
      apply (hoare_weak (icon Ps));
      first by Ent_R_flat_match_icon
  end.

Goal forall P Q R S, {{ P ** Q }} skip {{ R ** S }}.
move => *.
Hoare_R_to_icon.
Hoare_L_to_icon.
Abort.

Ltac Hoare_ifte_bang H :=
  match goal with
    | |- {{ _ }} If ?B Then _ Else _ {{ _ }} =>
      apply hoare_ifte_bang; [ set H := `! B | set H := `! \~b B]
  end.


Ltac Replace_list n l a :=
  match n with
    | O => match l with
             | nil => fail
             | cons ?hd ?tl => constr: (cons a tl)
           end
    | S ?m => match l with
                | nil => fail
                | cons ?hd ?tl =>
                  let tl' := Replace_list m tl a in constr: (cons hd tl')
              end
  end.

Ltac Remove_list n l :=
  match n with
    | O => match l with
               | nil => fail
               | cons ?hd ?tl => constr: (tl)
           end
    | S ?m => match l with
                | nil => fail
                | cons ?hd ?tl =>
                  let tl' := Remove_list m tl in constr: (cons hd tl')
              end
  end.

(* NB: see also Find_var *)
Ltac Find_index name lst :=
  match lst with
    | nil => fail
    | name :: _ => constr: (0)
    | _ :: ?tl => let i := Find_index name tl in constr: (i.+1)
  end.

Ltac Find_indices names lst :=
  match names with
    | nil => constr: (@Nil nat)
    | ?hd :: ?tl =>
      let hd' := Find_index hd lst in
      let tl' := Find_indices tl lst in
      constr: (hd' :: tl')
  end.

Ltac Ent_L_icon_Find_indices names :=
  match goal with | |- icon ?P ===> _ => Find_indices names P end.

Ltac Ent_R_icon_Find_indices names :=
  match goal with | |- _ ===> icon ?P => Find_indices names P end.

Ltac Hoare_L_Find_index n :=
  match goal with
    | |- {{ ?P }} _ {{ _ }} => let l' := assert_to_seq P in Find_index n l'
  end.

Ltac Hoare_L_Find_indices l :=
  match goal with
    | |- {{ ?P }} _ {{ _ }} => let l' := assert_to_seq P in Find_indices l l'
  end.

Ltac Ent_L_Find_indices l :=
  match goal with
    | |- ?P ===> _ => let l' := assert_to_seq P in Find_indices l l'
  end.

Ltac Hoare_R_icon_Find_indices names :=
  match goal with | |- {{ _ }} _ {{ icon ?P }} => Find_indices names P end.

Ltac Hoare_L_icon_Find_indices names :=
  match goal with | |- {{ icon ?P }} _ {{ _ }} => Find_indices names P end.

(* find occurence of assert types in list of assert (without emp) *)

Ltac Find_sepex_list_assert' l n :=
  match l with
    | nil => constr: (@Nil nat)
    | ?hd :: ?tl =>
      let i := Find_sepex_list_assert' tl (n.+1) in
      match hd with
        | (sepexists _) => constr: (n :: i)
        | _ => constr: (i)
      end
  end.

Ltac Find_sepex_list_assert l := Find_sepex_list_assert' l 0.

Ltac Find_sepall_list_assert' l n :=
  match l with
    | nil => constr: (@Nil nat)
    | ?hd :: ?tl =>
      let i := Find_sepall_list_assert' tl (n.+1) in
      match hd with
        | (sepforall _) => constr: (n :: i)
        | _ => constr: (i)
      end
  end.

Ltac Find_sepall_list_assert l := Find_sepall_list_assert' l 0.

Ltac Find_sepor_list_assert' l n :=
  match l with
    | nil => constr: (@Nil nat)
    | ?hd :: ?tl =>
      let i := Find_sepor_list_assert' tl (n.+1) in
      match hd with
        | (_ \\// _) => constr: (n :: i)
        | _ => constr: (i)
      end
  end.

Ltac Find_sepor_list_assert l := Find_sepor_list_assert' l 0.

Ltac Find_sbang_list_assert l :=
  match l with
    | nil => constr: (@Nil nat)
    | (sbang ?P) :: ?tl =>
      let i := Find_sbang_list_assert tl in
      eval vm_compute in (0 :: map S i)
    | _ :: ?tl =>
      let i := Find_sbang_list_assert tl in
      eval vm_compute in (map S i)
  end.

Ltac Find_ex n l :=
  match l with
    | nil => fail
    | cons (sepex _, _) _ => n
    | cons _ ?tl => Find_ex (S n) tl
  end.

Ltac Find_Or n l :=
  match l with
    | nil => fail
    | cons (Or _ _) _ => n
    | cons _ ?tl => Find_Or (S n) tl
  end.

(* m is the occurrence number *)
Ltac Find_sbang m n l :=
  match l with
    | nil => fail
    | cons (sbang _) ?tl => match m with O => n | S ?m' =>
       Find_sbang m' (S n) tl end
    | cons _ ?tl => Find_sbang m (S n) tl
  end.

Ltac Find_wp_assign_Or n l :=
  match l with
    | nil => fail
    | cons (wp_assign _ _ (Or _ _)) _ => n
    | cons _ ?tl => Find_wp_assign_Or (S n) tl
  end.

Ltac Find_wp_assign_ex n l :=
  match l with
    | nil => fail
    | cons (wp_assign _ _ (sepex _, _)) _ => n
    | cons _ ?tl => Find_wp_assign_ex (S n) tl
  end.

Ltac Find_wp_assign_sbang n l :=
  match l with
    | nil => fail
    | cons (wp_assign _ _ (!!( _ ))) _ => n
    | cons _ ?tl => Find_wp_assign_sbang (S n) tl
  end.

Ltac Find_bbang_eq_e count n l :=
  match l with
    | nil => constr: (@None nat)
    | (`! (exp2bexp _ (Ceq_eq_nosimpl _ _ _))) :: ?tl =>
      match n with
        | O => constr: (Some count)
        | S ?m => Find_bbang_eq_e (S count) m tl
      end
    | _ :: ?tl =>
      Find_bbang_eq_e (S count) n tl
  end.

Ltac Find_bbang_eq_p count n l :=
  match l with
    | nil => constr: (@None nat)
    | (`! (exp2bexp _ (Ceq_eq_nosimpl _ _ _))) :: ?tl =>
      match n with
        | O => constr: (Some count)
        | S ?m => Find_bbang_eq_p (S count) m tl
      end
    | _ :: ?tl =>
      Find_bbang_eq_p (S count) n tl
  end.

Lemma entails_trans2 P Q R : P ===> R -> Q ===> P -> Q ===> R.
Proof. move=> H1 H2. eapply ent_trans; eauto. Qed.

(* Replace the lhs of entails with a permutation *)
Ltac Ent_L_permut indices :=
  match goal with
    | |- icon ?P ===> _ =>
      generalize (@equiv_imp _ _
        (@Sum_rearrangement assert con assert_abelean P indices (refl_equal _)));
      rewrite -!iconE ; simpl icon ; apply entails_trans2
  end.

Lemma partitionL1 A Al Ar B Bl Br :
  (A <==> Al ** Ar) -> (B <==> Bl ** Br) -> (A ** B <==> (Al ** Bl) ** (Ar ** Br)).
Proof. move=> H1 H2. by rewrite conCA 2!conA (conC Ar) -H1 -conA -H2. Qed.

Lemma partitionL2 A A' B B' :
  (A <==> A') -> (B <==> B') -> (A ** B <==> A' ** B').
Proof. move=> H1 H2. by rewrite -H1 -H2. Qed.

Ltac decide_in x xs :=
  match xs with
    | x :: _ => constr: (true)
    | _ :: ?xs' => decide_in x xs'
    | nil => constr: (false)
  end.

Lemma coneP_sym A : A <==> emp ** A. Proof. by rewrite coneP. Qed.

Lemma conPe_sym A : A <==> A ** emp. Proof. by rewrite conPe. Qed.

Ltac partition xs P :=
  lazymatch P with
    | ?A ** ?B =>
      let Ha := fresh "H" in
      let Hb := fresh "H" in
      partition xs A => Ha;
      partition xs B => Hb;
      match goal with
        | Ha : _ <==> ?Al ** ?Ar, Hb : _ <==> ?Bl ** ?Br |- _ =>
          let Hl := fresh "H" in
          let Hr := fresh "H" in
          match constr: ((Al, Bl)) with
            | (emp, _) => move: (coneP Bl)
            | (_, emp) => move: (conPe Al)
            | _ => move: (equiv_refl (Al ** Bl))
          end; move => Hl;
          match constr: ((Ar, Br)) with
            | (emp, _) => move: (coneP Br)
            | (_, emp) => move: (conPe Ar)
            | _ => move: (equiv_refl (Ar ** Br))
          end; move => Hr;
          move: (equiv_trans _ _ _ (partitionL1 _ _ _ _ _ _ Ha Hb) (partitionL2 _ _ _ _ Hl Hr)) =>
            {Ha Hb Hl Hr}
      end
    | ?X =>
      let inl := decide_in X xs in
      match inl with
        | true => move: (conPe_sym X)
        | false => move: (coneP_sym X)
      end
  end.

Goal False.
  move: emp emp emp emp emp emp emp emp => A B C D E F G H.
  partition (B :: D :: nil) ((A ** B) ** (C ** D)).
Abort.

Definition remove_indices {T} (P : seq T) lst :=
  foldr (fun hd acc => delete1 acc hd) (iota 0 (size P)) lst.

Ltac Ent_L_icon_put_in_front lst :=
  match goal with
    | |- icon ?P ===> ?Q =>
      let new_indices := eval vm_compute in (lst ++ remove_indices P lst) in
      Ent_L_permut new_indices
  end.

Goal forall P Q R S, icon(P, Q, R, S) ===> R ** P ** Q ** S.
move=> P Q R S.
Ent_L_icon_put_in_front (2 :: nil).
Abort.

Ltac Ent_R_permut indices :=
match goal with
| |- _ ===> icon ?Q =>
  generalize (@equiv_imp2 _ _
    (@Sum_rearrangement assert con assert_abelean Q indices (refl_equal _)));
  rewrite -!iconE ; simpl icon ; apply ent_trans
end.

Ltac Ent_R_icon_put_in_front lst :=
  match goal with
    | |- ?Q ===> icon ?P =>
      let new_indices := eval vm_compute in (lst ++ remove_indices P lst) in
      Ent_R_permut new_indices
  end.

Goal forall P Q R S, R ** P ** Q ** S ===> icon(P, Q, R, S).
move=> P Q R S.
by Ent_R_icon_put_in_front (2 :: nil).
Abort.

Ltac Ent_LR_icon_put_in_front l1 l2 :=
  Ent_L_icon_put_in_front l1; Ent_R_icon_put_in_front l2.

Ltac Ent_L_icon_put_in_back lst :=
  match goal with
    | |- icon ?P ===> _ =>
      let new_indices := eval vm_compute in (remove_indices P lst ++ lst) in
      Ent_L_permut new_indices
  end.

Ltac Ent_R_icon_put_in_back lst :=
  match goal with
    | |- _ ===> icon ?P  =>
      let new_indices := eval vm_compute in (remove_indices P lst ++ lst) in
      Ent_R_permut new_indices
  end.

Ltac Ent_LR_icon_put_in_back l1 l2 :=
  Ent_L_icon_put_in_back l1; Ent_R_icon_put_in_back l2.

Ltac Hoare_L_permut indices :=
  match goal with
    | |- {{ icon ?P }} _ {{ _ }} =>
      let H := fresh in
      generalize (@equiv_imp _ _
        (@Sum_rearrangement assert con assert_abelean P indices (refl_equal _))) ;
      rewrite -!iconE ;
      simpl icon ;
      intro H ;
      apply (@hoare_stren _ _ _ _ H) ; clear H
  end.

Ltac Hoare_L_icon_put_in_front lst :=
  match goal with
    | |- {{ icon ?P }} _ {{ _ }} =>
      let new_indices := eval vm_compute in (lst ++ remove_indices P lst) in
      Hoare_L_permut new_indices
  end.

Ltac Hoare_R_permut indices :=
  match goal with
    | |- {{ _ }} _ {{ icon ?Q }} =>
      let H := fresh in
      generalize (@equiv_imp2 _ _
        (@Sum_rearrangement assert con assert_abelean Q indices (refl_equal _))) ;
      rewrite -!iconE ;
      simpl icon ;
      intro H ;
      apply (@hoare_weak _ _ _ _ H) ; clear H
  end.

Ltac Hoare_R_icon_put_in_front lst :=
  match goal with
    | |- {{ _ }} _ {{ icon ?P }} =>
      let new_indices := eval vm_compute in (lst ++ remove_indices P lst) in
      Hoare_R_permut new_indices
  end.

Ltac Hoare_R_icon_put_in_back lst :=
  match goal with
    | |- {{ _ }} _ {{ icon ?P }} =>
      let new_indices := eval vm_compute in (remove_indices P lst ++ lst) in
      Hoare_R_permut new_indices
end.

Ltac Hoare_L_icon_put_in_back lst :=
  match goal with
    | |- {{ icon ?P }} _ {{ _ }} =>
      let new_indices := eval vm_compute in (remove_indices P lst ++ lst) in
      Hoare_L_permut new_indices
end.

Lemma monotony_icon P Q R S : icon P  ===> icon Q  ->
  icon R ===> icon S -> icon ( P ++ R ) ===> icon ( Q ++ S ).
Proof.
rewrite /icon !Sum_cat => P_Q R_S.
by rewrite -> R_S, P_Q.
Qed.

Ltac Ent_decompose_icon l1 l2 :=
  Ent_LR_icon_put_in_front l1 l2;
  let sz1 := eval vm_compute in (size l1) in
  let sz2 := eval vm_compute in (size l2) in
  match goal with
    | |- icon ?P ===> icon ?Q =>
      rewrite -(cat_take_drop sz1 P) -(cat_take_drop sz2 Q); apply monotony_icon
  end.

Ltac Ent_decompose l1 l2 :=
  Ent_LR_to_icon; Ent_decompose_icon l1 l2; unfold icon; simpl.

(* NB: Solve_permutation tactic comes from seq_ext.v *)
Ltac Ent_permut :=
  match goal with
    | |- ?X ===> ?Y =>
      Ent_LR_to_icon; apply icon_morphism_entails; simpl;
      Solve_permutation
  end.

Goal forall P Q R, P ** Q ** R ** P ===> R ** P ** Q ** P.
  move => P Q R.
  Ent_permut.
Abort.

Fixpoint seq_replace {A : Type} (l : seq A) (e : A) (i : nat) : seq A :=
  match l with
    | nil => nil
    | hd :: tl => if i == 0 then e :: tl else  hd :: seq_replace tl e i.-1
  end.

Ltac Find_common_prefix P Q i :=
  match Q with
    | ?hd :: ?tl =>
      let j := Find_index hd P in
      let P' := eval simpl in (seq_replace P emp j) in
      let next := Find_common_prefix P' tl (i.+1) in
        match next with
          | (?ileft, ?iright) => eval simpl in (j :: ileft, i :: iright)
        end
    | _ :: ?tl => Find_common_prefix P tl (i.+1)
    | _ => constr: ((Nil nat, Nil nat))
  end.

Ltac Ent_monotony_icon :=
  match goal with
    | |- icon ?P ===> icon ?Q =>
      match Find_common_prefix P Q 0 with
        | (?indices_l, ?indices_r) =>
          Ent_decompose_icon indices_l indices_r; [|] => //=
      end
  end.

Ltac Ent_monotony := Ent_LR_to_icon; Ent_monotony_icon; unfold icon; simpl.

Tactic Notation "Ent_monotony0_new" tactic(tac) :=
  repeat (tac || apply monotony_R || apply monotony_L || apply monotony_R2 || apply monotony_L2);
  try (apply ent_emp_bbang_pe || apply ent_emp_bbang_re).

Ltac Ent_monotony0 := Ent_monotony0_new fail.

Goal forall P Q R S, P ** Q ** R ** P ===> R ** P ** S ** Q ** P.
  move => P Q R S.
  Ent_monotony.
Abort.

Local Open Scope zarith_ext_scope.

(** sbang *)

Lemma ent_L_icon_sbang (P : Prop) (Q : seq assert) (R : assert) :
  (P -> (icon Q  ===> R)) -> icon (!!(P) :: Q) ===> R.
Proof. move=> H. eapply ent_trans; by [apply icon_cons | apply ent_L_sbang_con]. Qed.

Lemma ent_R_icon_sbang (P : Prop) (Q : seq assert) (R : assert):
  P -> (R ===> icon Q) -> R ===> icon (!!(P) :: Q).
Proof.
move=> H1 H2. eapply ent_trans; first by exact H2.
eapply ent_trans; last by apply cons_icon.
by apply ent_R_sbang_con.
Qed.

Ltac Ent_L_sbang_icon n :=
  match goal with
    | |- icon ?P ===> _ =>
      let indices := Find_sbang_list_assert P in
      match indices with
        | nil => fail "no sbang in l.h.s. of entails"
        | _ =>
          let i := eval simpl in (nth 0%nat indices n) in
          Ent_L_icon_put_in_front (i :: nil); apply ent_L_icon_sbang
      end
  end.

Ltac Ent_L_sbang n :=
  Ent_L_to_icon; Ent_L_sbang_icon n; rewrite iconE /=.

Ltac Ent_R_sbang_icon n :=
  match goal with
    | |- _ ===> icon ?P =>
      let indices := Find_sbang_list_assert P in
        match indices with
          | nil => fail "no sbang in r.h.s. of entails"
          | _ =>
            let i := eval simpl in (nth 0%nat indices n) in
            Ent_R_icon_put_in_front (i :: nil); apply ent_R_icon_sbang
        end
  end.

Ltac Ent_R_sbang n :=
  Ent_R_to_icon; Ent_R_sbang_icon n; last rewrite iconE /=.

Ltac Ent_R_sbang_all :=
  try (Ent_R_sbang 0; [ idtac | Ent_R_sbang_all]).

Ltac Hoare_L_sbang n :=
  match goal with
    | |- {{ icon ?P }} ?c {{ _ }} =>
      let indices := Find_sbang_list_assert P in
        match indices with
          | nil => fail "no sbang in precond"
          | _ => let i := eval simpl in (nth 0%nat indices n) in
            Hoare_L_icon_put_in_front (i :: nil)
        end
    | |- {{ ?P }} ?c {{ _ }} =>
      let X := fresh in
      (set X := c);
      Hoare_L_to_icon;
      Hoare_L_sbang n; rewrite iconE /=; unfold X; clear X;
      try (* TODO: remove? *)apply hoare_pullout_sbang
  end.

Ltac Hoare_R_sbang n :=
  match goal with
    | |- {{ _ }} ?c {{ icon ?P }} =>
      let indices := Find_sbang_list_assert P in
        match indices with
          | nil => fail "no sbang in precond"
          | _ => let i := eval simpl in (nth 0%nat indices n) in
            Hoare_R_icon_put_in_front (i::nil)
        end
    | |- {{ _ }} ?c {{ ?P }} =>
      let X := fresh in
      (set X := c);
      Hoare_R_to_icon;
      Hoare_R_sbang n; rewrite iconE /=; unfold X; clear X;
      try (* TODO: remove? *) apply hoare_pullout_sbang_postcond
  end.

Ltac Ent_L_sbang_all :=
  try (Ent_L_sbang 0; Ent_L_sbang_all).

Lemma bbang_re_to_wp_assign {t} str {str_t : assoc_get str sigma = Some (ityp: t)}
  (e : exp sigma (ityp: t)) P Q :
  icon (map (fun x => wp_assign str_t e x) P) ===> wp_assign str_t e Q ->
  icon ( (`! \b var_e _ _ _ str_t \= e) :: P ) ===> Q.
Proof.
rewrite iconE => icon_P.
rewrite iconE Sum_cons => s h [h1 h2 h1dh2 Hh1 Hh2].
move/bbang_eqi_store_get : (Hh1) => Hh1'.
rewrite <- Sum_distrib in icon_P; last 3 first.
  by apply wp_assign_morphism.
  by apply wp_assign_emp.
  by apply wp_assign_con.
have H2 : wp_assign str_t e (@Sum _ con assert_abelean P) s h2.
  apply wp_assign_c.
  by rewrite (_ : store_upd _ _ _ = s) // -Hh1' store_upd_get_eq.
have : wp_assign str_t e Q s h2 by apply icon_P.
inversion_clear 1.
rewrite -Hh1' store_upd_get_eq in H.
case: (Hh1) => _.
rewrite /emp => ->.
by rewrite hp.unioneh.
Qed.

Ltac Ent_rewrite_eq_e_icon n lemma :=
  match goal with
    | |- icon ?P ===> _ =>
      let idx := Find_bbang_eq_e O n P in
      match idx with
        | None => fail "no bbang eq_e in l.h.s. of entails"
        | Some ?i =>
            Ent_L_icon_put_in_front (i :: nil);
            apply lemma
        end
  end.

Ltac Ent_LR_rewrite_eq_e_icon n :=
  Ent_rewrite_eq_e_icon n bbang_re_to_wp_assign.

Ltac Ent_LR_rewrite_eq_e n :=
  Ent_L_to_icon; Ent_LR_rewrite_eq_e_icon n; rewrite iconE /=.

(* NB: fait disparaitre l'egalite qui sert au rewrite,
       ne reecrit que dans le rhs *)
Lemma bbang_re_to_wp_assign' {t} str {str_t : assoc_get str sigma = Some (ityp: t)}
  (e : exp sigma (ityp: t)) P Q :
  icon P ===> wp_assign str_t e Q ->
  icon ( (`! \b var_e _ _ _ str_t \= e) :: P ) ===> Q.
Proof.
rewrite iconE => icon_P.
rewrite iconE Sum_cons => s h [h1 h2 h1dh2 Hh1 Hh2].
move/bbang_eqi_store_get : (Hh1) => Hh1'.
have H2 : wp_assign str_t e (@Sum _ con assert_abelean P) s h2.
  apply wp_assign_c.
  by rewrite (_ : store_upd _ _ _ = s) // -Hh1' store_upd_get_eq.
have : wp_assign str_t e Q s (h1 \U h2).
  by rewrite (proj2 Hh1) hp.unioneh; apply icon_P.
inversion_clear 1; by rewrite -Hh1' store_upd_get_eq in H.
Qed.

Ltac Ent_R_rewrite_bbang_re_icon n :=
  Ent_rewrite_eq_e_icon n bbang_re_to_wp_assign'.

Ltac Ent_R_rewrite_eq_e n :=
  Ent_L_to_icon; Ent_R_rewrite_bbang_re_icon n; rewrite iconE /=.

Lemma bbang_pe_to_wp_assign {ty : g.-typ} str {Hstr : assoc_get str sigma = Some (:* ty)}
  (e : exp sigma (:* ty)) P Q :
  icon (map (fun P => wp_assign Hstr e P) P) ===>
  wp_assign Hstr e Q ->
  icon ( (`! \b @var_e g _ str (:* ty) Hstr \= e ) :: P ) ===> Q.
Proof.
rewrite iconE => icon_P.
rewrite <- Sum_distrib in icon_P; last 3 first.
  by apply wp_assign_morphism.
  by apply wp_assign_emp.
  by apply wp_assign_con.
rewrite iconE Sum_cons => s h [h1 h2 h1dh2 Hh1 Hh2].
move/bbang_eqp_store_get : (Hh1) => Hh1'.
case: (Hh1) => _.
rewrite /emp => ?; subst h1.
rewrite hp.unioneh.
have H2 : wp_assign Hstr e (@Sum _ con assert_abelean P) s h2.
  apply wp_assign_c.
  by rewrite (_ : store_upd _ _ _ = s) // -Hh1' store_upd_get_eq.
have : wp_assign Hstr e Q s h2 by apply icon_P, H2.
inversion_clear 1; by rewrite -Hh1' store_upd_get_eq in H.
Qed.

Ltac Ent_rewrite_eq_p_icon n lemma :=
  match goal with
    | |- icon ?P ===> _ =>
      let idx := Find_bbang_eq_p O n P in
      match idx with
        | None => fail "no bbang eq_p in l.h.s. of entails"
        | Some ?i =>
            Ent_L_icon_put_in_front (i :: nil);
            apply lemma
        end
  end.

Ltac Ent_LR_rewrite_eq_p_icon n :=
  Ent_rewrite_eq_p_icon n bbang_pe_to_wp_assign.

Ltac Ent_LR_rewrite_eq_p n :=
  Ent_L_to_icon; Ent_LR_rewrite_eq_p_icon n; rewrite iconE /=.

(* same but rewriting only in r.h.s. *)
Lemma bbang_pe_to_wp_assign' {ty : g.-typ} str {Hstr : assoc_get str sigma = Some (:* ty)}
  (e : exp sigma (:* ty)) P Q :
  icon P ===>
  wp_assign Hstr e Q ->
  icon ( (`! \b @var_e g _ str (:* ty) Hstr \= e ) :: P ) ===> Q.
Proof.
rewrite iconE => icon_P.
rewrite iconE Sum_cons => s h [h1 h2 h1dh2 Hh1 Hh2].
move/bbang_eqp_store_get : (Hh1) => Hh1'.
case: (Hh1) => _.
rewrite /emp => ?; subst h1.
rewrite hp.unioneh.
have : wp_assign Hstr e Q s h2 by apply icon_P.
inversion_clear 1; by rewrite -Hh1' store_upd_get_eq in H.
Qed.

Ltac Ent_R_rewrite_eq_p_icon n := Ent_rewrite_eq_p_icon n bbang_pe_to_wp_assign'.

Ltac Ent_R_rewrite_eq_p n :=
  Ent_L_to_icon; Ent_R_rewrite_eq_p_icon n; rewrite iconE /=.

Ltac Rewrite_ground_bexp H :=
  eapply ground_bexp_morphism; [ rewrite H; first by reflexivity | done | instantiate (1 := refl_equal _)].

(** Ground bang *)

Ltac Bbang2sbang_loop P :=
  match P with
    | (`! ?b) => try rewrite -> (@ground_bbang_sbang b (refl_equal _))
    | ?Q ** ?R => Bbang2sbang_loop Q; Bbang2sbang_loop R
    | _ => idtac
  end.

Ltac Bbang2sbang :=
  match goal with
    | |- ?P ===> ?Q => Bbang2sbang_loop P; Bbang2sbang_loop Q
  end.

(** sepex *)

Lemma ent_L_ex_icon {A} (P : A -> assert) Q R :
  (forall x, icon ( P x :: Q ) ===> R) -> icon ( (sepex x, P x) :: Q ) ===> R.
Proof.
move=> H.
eapply ent_trans; first by apply icon_cons.
apply ent_L_ex1 => a.
eapply ent_trans; by [apply cons_icon | apply H].
Qed.

Lemma ent_R_ex_icon {A} (P : A -> assert) Q R :
  (exists x, R ===> icon ( P x :: Q )) -> R ===> icon ( (sepex x, P x) :: Q ).
Proof.
case=> a H.
eapply ent_trans; last by apply cons_icon.
apply ent_R_ex1; exists a.
eapply ent_trans; by [apply icon_cons | apply H].
Qed.

Ltac Ent_L_ex_n_icon n :=
  match goal with
    | |- icon ?P ===> _ =>
      let indices := Find_sepex_list_assert P in
      match indices with
        | nil => fail "no sepex in l.h.s. of entails"
        | _ =>
          let i := eval simpl in (nth 0%nat indices n) in
            Ent_L_icon_put_in_front (i :: nil); apply ent_L_ex_icon
      end
  end.

Ltac Ent_L_ex_n n H :=
  Ent_L_to_icon; Ent_L_ex_n_icon n; intro H; rewrite iconE /=.

Ltac Ent_L_flat_match_n_gen tac :=
match goal with
| |- (?Q1 ** ?Q2) ** ?Q3 ===> ?Q =>
  refine (ent_trans _ _ Q (equiv_imp2 _ _ (conA Q1 Q2 Q3)) _) ;
  Ent_L_flat_match_n_gen tac
| |- _ ** (sepex _, _) ** _ ===> _ => idtac
| |- ?Q1 ** ?Q2 ===> _ => tac; Ent_L_flat_match_n_gen tac
| |- _ ===> _ => idtac
end.

Ltac Ent_L_flat_match_n := Ent_L_flat_match_n_gen Ent_L_flat_match_tac.

Ltac Ent_L_flat_n :=
  match goal with
    | |- ?P ===>  _ =>
      let P' := assert_to_seq P in
          eapply ent_trans; [ Ent_L_flat_match_n ; apply ent_id | idtac ]
  end.

Ltac Ent_L_deflat_match_n_gen n tac :=
match n with
| S ?n' =>
match goal with
| |- ?Q1 ** ?Q2 ** ?Q3 ===> ?Q =>
  refine (ent_trans _ _ Q (equiv_imp _ _ (conA Q1 Q2 Q3)) _) ;
  Ent_L_deflat_match_n_gen n' tac
| |- ?Q1 ** ?Q2 ===> _ => tac; Ent_L_deflat_match_n_gen n' tac
| |- _ ===> _ => idtac
end
| O => idtac
end.

Ltac Ent_L_deflat_match_n n := Ent_L_deflat_match_n_gen n Ent_L_flat_match_tac.

Ltac Ent_L_deflat_n :=
  match goal with
    | |- ?P ===>  _ =>
      let P' := assert_to_seq P in
      let n := Find_ex O P' in
      match n with
        | O => idtac
        | S ?n' =>
          eapply ent_trans; [ Ent_L_deflat_match_n n' ; apply ent_id | idtac ]
      end
  end.

Ltac Ent_L_ex param :=
  match goal with
    |- _ ===> _ =>
    Ent_L_flat_n ;
    Ent_L_deflat_n ;
  match goal with
    |- ?Q ===> _ =>
    match Q with
      | _ ** (sepex _, _) ** _ => apply ent_L_ex2; intro param
      | (sepex _ , _)  ** _ => apply ent_L_ex1; intro param
      | _ ** (sepex _, _) => apply ent_L_ex1'; intro param
      | (sepex _, _) => apply ent_L_ex0; intro param
    end
  end
end.

Ltac Ent_R_ex_n_icon n :=
  match goal with
    | |- _ ===> icon ?P =>
      let indices := (Find_sepex_list_assert P) in
      match indices with
        | nil => fail "no sepex in l.h.s. of entails"
        | _ =>
          let i := eval simpl in (nth 0%nat indices n) in
            Ent_R_icon_put_in_front (i::nil); apply ent_R_ex_icon
      end
  end.

Ltac Ent_R_ex_n n H :=
  Ent_R_to_icon; Ent_R_ex_n_icon n; exists H; rewrite iconE /=.

Lemma hoare_R_ex_icon (A : Type) P (Q : A -> assert) R c :
  (exists y, {{ P }} c {{ icon (Q y ::  R) }}) -> {{ P }} c {{ icon ((sepex x, Q x) :: R) }}.
Proof.
case=> a H.
eapply hoare_weak; last by apply H.
eapply ent_trans; first by apply icon_cons.
apply ent_R_ex_icon.
exists a; by apply cons_icon.
Qed.

Lemma hoare_L_ex_icon (A : Type) P (Q : A -> assert) R c :
  (forall y, {{ icon (Q y :: P) }} c {{ R }}) -> {{ icon ((sepex x, Q x) :: P) }} c {{ R }}.
Proof.
move=> Hhoare.
rewrite /icon !Sum_cons.
apply hoare_complete => s h [h1 h2 h1dh2 [x Hh1] Hh2].
apply (soundness _ _ _ (Hhoare x)).
rewrite iconE.
rewrite (@Sum_cons _ _ assert_abelean _ _ s (h1 \U h2)).
(* TODO: assert_abelean should be inferred automatically *)
by apply con_c.
Qed.

Ltac Hoare_L_ex_icon n :=
  match goal with
    | |- {{ icon ?P }} _ {{ _ }} =>
      let indices := (Find_sepex_list_assert P) in
      match indices with
        | nil => fail "no sepex in precond"
        | _ =>
          let i := eval simpl in (nth 0%nat indices n) in
            Hoare_L_icon_put_in_front (i::nil); apply hoare_L_ex_icon
      end
  end.

(** pulls the nth exists from the precond (to be named H) *)
Ltac Hoare_L_ex n H :=
match goal with
  | |- {{ _ }} ?c {{ _ }} =>
    let x := fresh in
      (set x := c);
      Hoare_L_to_icon; Hoare_L_ex_icon n; intro H; rewrite iconE /=; unfold x; clear x
end.

Ltac Hoare_R_ex_icon n :=
  match goal with
    | |- {{ _ }} _ {{ icon ?P }} =>
      let indices := (Find_sepex_list_assert P) in
      match indices with
        | nil => fail "no sepex in l.h.s. of entails"
        | _ =>
          let i := eval simpl in (nth 0%nat indices n) in
            Hoare_R_icon_put_in_front (i::nil); apply hoare_R_ex_icon
      end
  end.

Ltac Hoare_R_ex n H :=
  match goal with
    | |- {{ _ }} ?c {{ _ }} =>
      let x := fresh in
        (set x := c);
        Hoare_R_to_icon; Hoare_R_ex_icon n; exists H; rewrite iconE /=; unfold x; clear x
end.

(** sepor *)

Lemma ent_L_or_icon (P Q : assert) R S :
  icon ( P :: R ) ===> S -> icon ( Q :: R ) ===> S ->
  icon ( (P \\// Q) :: R ) ===> S.
Proof.
move=> H1 H2.
eapply ent_trans; first by apply icon_cons.
move/(ent_trans _ _ _ (cons_icon _ _)) in H1.
move/(ent_trans _ _ _ (cons_icon _ _)) in H2.
by rewrite conDl; move=> s h []; move: s h.
Qed.

Ltac Ent_L_or_icon n :=
  match goal with
    | |- icon ?P ===> ?Q =>
      let sepors := Find_sepor_list_assert P in
        match sepors with
          | nil => fail "no sepor in l.h.s. of entails"
          | _ =>
            let i := eval simpl in (nth 0%nat sepors n) in
              Ent_L_icon_put_in_front (i :: nil);
              apply ent_L_or_icon
        end
  end.

Ltac Ent_L_or n := Ent_L_to_icon; Ent_L_or_icon n; rewrite iconE /=.

Lemma ent_R_or_2_icon (P Q : assert) R S :
  S ===> icon (Q :: R) -> S ===> icon ( (P \\// Q) :: R).
Proof.
move=> H.
eapply ent_trans; last by apply cons_icon.
eapply ent_trans; first by apply H.
eapply ent_trans; first by apply icon_cons.
by apply monotony_R, ent_R_or_2, ent_id.
Qed.

Lemma ent_R_or_1_icon (P Q : assert) R S :
  S ===> icon (P :: R) -> S ===> icon ( (P \\// Q) :: R).
Proof.
move=> H.
eapply ent_trans; last by apply cons_icon.
eapply ent_trans; first by apply H.
eapply ent_trans; first by apply icon_cons.
by apply monotony_R, ent_R_or_1, ent_id.
Qed.

Ltac Ent_R_or_1_n_icon n :=
  match goal with
    | |- ?P ===> icon ?Q =>
      let sepors := Find_sepor_list_assert Q in
        match sepors with
          | nil => fail "no sepor in l.h.s. of entails"
          | _ =>
            let i := eval simpl in (nth 0%nat sepors n) in
              Ent_R_icon_put_in_front (i :: nil);
              apply ent_R_or_1_icon
        end
  end.

Ltac Ent_R_or_1_n n := Ent_R_to_icon; Ent_R_or_1_n_icon n; rewrite iconE /=.

Ltac Ent_R_or_2_n_icon n :=
  match goal with
    | |- ?P ===> icon ?Q =>
      let sepors := Find_sepor_list_assert Q in
        match sepors with
          | nil => fail "no sepor in l.h.s. of entails"
          | _ =>
            let i := eval simpl in (nth 0%nat sepors n) in
              Ent_R_icon_put_in_front (i :: nil);
              apply ent_R_or_2_icon
        end
  end.

Ltac Ent_R_or_2_n n := Ent_R_to_icon; Ent_R_or_2_n_icon n; rewrite iconE /=.

(* begin new *)

Require Import Coq.Program.Tactics.

(* TODO: rename -> replace *)
Ltac Ent_R_gen param tac tac_idx :=
  match goal with
    |- _ ===> ?Q =>
    let Q' := assert_to_seq Q in
    let n := tac_idx O Q' in
    let R := fresh in
    evar (R : assert) ;
    let Q'' := Replace_list n Q' R in
    let Q3 := seq_to_assert Q'' in
    let n' := eval compute in (size Q' - S n)%nat in
    apply (ent_trans Q3); 
      [ idtac |
        (let tmp := (apply monotony_L) in do_nat n tmp) ;
        (match n' with S _ => apply monotony_R | _ => idtac end) ;
        tac param
      ] ;
    unfold R; clear R
  end.

Ltac Ent_R_wp_assign_or_tac param := now apply (equiv_imp2 _ _ (wp_assign_or _ _ _ _)).

Ltac Ent_R_wp_assign_or := Ent_R_gen tt Ent_R_wp_assign_or_tac Find_wp_assign_Or.

Ltac Ent_R_or_2_tac param := now refine (ent_R_or_2 _ _ _ (ent_id _)).

Ltac Ent_R_or_2 := Ent_R_gen tt Ent_R_or_2_tac Find_Or.

Ltac Ent_R_or_1_tac param :=
  apply ent_R_or_1; match goal with |- _ ===> ?B => exact (ent_id B) end.
(* NB: instead of
now refine (ent_R_or_1 _ _ _ (ent_id _)).
that seems to do superfluous infolds
*)

Ltac Ent_R_or_1 := Ent_R_gen tt Ent_R_or_1_tac Find_Or.

Ltac Ent_R_wp_assign_ex_tac param := now apply (equiv_imp2 _ _ (@wp_assign_ex _ _ _ _ _ _)).

Ltac Ent_R_wp_assign_ex := Ent_R_gen tt Ent_R_wp_assign_ex_tac Find_wp_assign_ex.

Definition typeOf {T} & T := T.

Ltac Ent_R_ex_tac param :=
  refine (@ent_R_ex0 (typeOf param) _ _ (ex_intro _ param _)).

Ltac Ent_R_ex n :=
Ent_R_gen n Ent_R_ex_tac Find_ex; [ | apply ent_id].

Ltac Ent_R_wp_assign_sbang_tac param := now apply (equiv_imp2 _ _ (wp_assign_sbang _ _ _)).

Ltac Ent_R_wp_assign_sbang := Ent_R_gen tt Ent_R_wp_assign_sbang_tac Find_wp_assign_sbang.

(* TODO: generalize, it is specialized to sbang *)
Ltac Ent_R_remove_gen m (*the mth occurrence of sbang *) param tac tac_idx :=
  match goal with
    |- _ ===> ?Q =>
    let Q' := assert_to_seq Q in
    let n := tac_idx m (* the mth occurrence of sbang *) O Q' in
    let R := fresh in
    let Q'' := Remove_list n Q' in
    let Q3 := seq_to_assert Q'' in
    let n' := eval compute in (size Q' - S n)%nat in
    let szQ' := eval compute in (size Q') in
    apply (ent_trans Q3);
      [ idtac |
        match szQ' with
          | S O => tac param
          | _ =>
            match n with
              | O => apply (equiv_imp2 _ _ (con_sbang_L _ _ param))
              | _ =>
                match n' with
                  | O =>
                    (let tmp := (apply monotony_L) in do_nat (n - 1)%nat tmp) ;
                      apply (equiv_imp2 _ _ (con_sbang_R _ _ param))
                  | _ =>
                    (let tmp := (apply monotony_L) in do_nat n tmp) ;
                      apply (equiv_imp2 _ _ (con_sbang_L _ _ param))
                end
            end
        end
      ]
  end.

Ltac Ent_R_sbang_tac param := now refine (equiv_imp2 _ _ (sbang_emp _ param)).

Ltac Ent_R_remove_sbang m (* the mth occurrence of the sbang *) param :=
  Ent_R_remove_gen m param Ent_R_sbang_tac Find_sbang.

(* end new *)

Lemma hoare_L_or_icon Q P S R c :
  {{ icon ( P :: R ) }} c {{ Q }} -> {{ icon ( S :: R ) }} c {{ Q }} ->
  {{ icon ( (P \\// S) :: R )  }} c {{ Q }}.
Proof.
move=> H1 H2.
eapply hoare_stren; last first.
  apply hoare_L_or.
  by apply H1.
  by apply H2.
eapply ent_trans; first by apply icon_cons.
rewrite conDl => s h [] /cons_icon H.
by left.
by right.
Qed.

Ltac Hoare_L_or_icon n :=
  match goal with
    | |- {{ icon ?P }} _ {{ _ }} =>
      let sepors := Find_sepor_list_assert P in
        match sepors with
          | nil => fail "no sepor in l.h.s. of entails"
          | _ => let i := eval simpl in (nth 0%nat sepors n) in
            Hoare_L_icon_put_in_front (i :: nil);
            apply hoare_L_or_icon
        end
  end.

Ltac Hoare_L_or n :=
  match goal with
    | |- {{ ?P }} ?c {{ _ }} =>
      let x := fresh in
        (set x := c);
        Hoare_L_to_icon; Hoare_L_or_icon n; rewrite iconE /=; unfold x; clear x
  end.

(** independence *)

(* dans l on va mettre les variables qui apparaissent dans P et on
   saura en plus qu'elles sont pas modifiees par le programme *)
Definition inde_cmd_refl (c : cmd) (P : seq assert) (l : seq string) :=
  all (fun s => s \notin l) (unzip1 (modified_vars c)) /\
  inde_cmd c (icon P).

Lemma inde_cmd_refl_in c P : inde_cmd_refl c P nil -> inde_cmd c (icon P).
Proof. by case. Qed.

Lemma inde_cmd_refl_out c l :
  all (fun s => s \notin l) (unzip1 (modified_vars c)) -> inde_cmd_refl c nil l.
Proof. by move => H; split. Qed.

Lemma inde_cmd_icon c P : inde_cmd c (icon (P :: nil)) -> inde_cmd c P.
Proof.
rewrite /inde_cmd /inde => /= H s h x t v H0.
by case: {H}(H s h x t v H0).
Qed.

Lemma inde_cmd_refl_head_con c l P Q R :
  inde_cmd_refl c (P::Q::R) l -> inde_cmd_refl c ((P ** Q)::R) l.
Proof.
by rewrite /inde_cmd_refl; rewrite /icon !Sum_cons conA.
Qed.

Lemma inde_cmd_refl_head_or c l P Q R :
  inde_cmd_refl c (P::nil) nil -> inde_cmd_refl c (Q::nil) nil ->
  inde_cmd_refl c R l -> inde_cmd_refl c ((P \\// Q)::R) l.
Proof.
move => H1 H2 H3.
rewrite /inde_cmd_refl.
split; first by apply (proj1 H3).
rewrite /icon Sum_eq4.
apply inde_cmd_cons.
split; last by apply (proj2 H3).
apply inde_cmd_sepor; split; [apply (proj2 H1) | apply (proj2 H2)].
Qed.

Class NonEmpty (A: Type) := {
   eg: A
}.

Instance NonEmpty_nat: NonEmpty nat.
constructor.
exact 0.
Qed.

Instance NonEmpty_int {n}: NonEmpty (int n).
constructor.
exact (Z2u n 0).
Qed.

Lemma inde_cmd_refl_head_ex {A} {H : NonEmpty A} c l (P: A -> assert) Q :
  (forall x, inde_cmd_refl c ((P x) :: Q) l) ->
  inde_cmd_refl c ((sepex x, P x) :: Q) l.
Proof.
move => Hx; split.
  have : inde_cmd_refl c (P (@eg _ H) :: Q) l by apply (Hx eg).
  case; tauto.
rewrite iconE Sum_eq4 -iconE exists_left_prenex.
move => s h x ty v H0; split.
- inversion_clear 1.
  exists x0.
  move: (Hx x0) => {Hx}.
  inversion_clear 1.
  rewrite iconE in H3.
  rewrite -> Sum_eq4 in H3.
  rewrite -iconE in H3.
  by move: (proj1 (H3 _ _ _ _ v H0) H2).
- inversion_clear 1.
  exists x0.
  move: (Hx x0) => {Hx}.
  inversion_clear 1.
  rewrite iconE in H3.
  rewrite -> Sum_eq4 in H3.
  rewrite -iconE in H3.
  by apply (proj2 (H3 _ _ _ _ v H0) H2).
Qed.

Lemma inde_cmd_refl_cons c tl hd l : inde_cmd c hd /\ inde_cmd_refl c tl l ->
  inde_cmd_refl c (hd::tl) l.
Proof.
case=> H1 H2.
red; red in H2.
split; first by tauto.
rewrite iconE Sum_cons.
apply inde_cmd_cons; tauto.
Qed.

Lemma inde_cmd_refl_head c l P Q lP HlP : @only_dep lP HlP P ->
  inde_cmd_refl c Q (l ++ (unzip1 lP)) -> inde_cmd_refl c (P::Q) l.
Proof.
move => Hdep H.
apply inde_cmd_refl_cons.
inversion_clear H.
split.
- eapply (@only_dep_inde_cmd _ _ _ _ Hdep _ (refl_equal _)).
  apply (@all_impl_prop _ (fun s : string_eqType => s \notin l ++ unzip1 lP)) => //=.
  move => x; apply/implyP.
  rewrite mem_cat.
  by case: (x \in unzip1 lP); first rewrite /= orbT.
- red.
  split => //.
  apply (@all_impl_prop _ (fun s : string_eqType => s \notin l ++ unzip1 lP)) => //=.
  move => x; apply/implyP.
  rewrite mem_cat.
  by case: (x \in l).
Qed.

(* TODO this cases never appear*)
(*
| |- only_dep _ _ (sepexists ?P) => eapply sepex_only_dep; intro; Only_dep
| |- only_dep _ _ (?P ** ?Q) => eapply con_only_dep;Only_dep
| |- only_dep _ _ (?P \\// ?Q) => eapply sepor_only_dep;Only_dep
*)

Ltac Inde_cmd_refl :=
  match goal with
    | |- inde_cmd_refl ?c ((`! ?b)::?Q) ?l =>
      apply (inde_cmd_refl_head c l (`! b) Q (bvars b) (bvars_subset_sigma b) (@bbang_only_dep b));
simpl_inde_cmd_refl_head_output;
      Inde_cmd_refl
    | |- inde_cmd_refl ?c ((?e |--> ?l')::?Q) ?l =>
      apply (inde_cmd_refl_head c l (e |--> l') Q (vars e) (vars_in_ts e) (@mapstos_only_dep _ e l'));
simpl_inde_cmd_refl_head_output;
      Inde_cmd_refl
    | |- inde_cmd_refl ?c ((?e |---> ?l')::?Q) ?l =>
      apply (inde_cmd_refl_head c l (e |---> l') Q (vars e) (vars_in_ts e) (@mapstos_fit_only_dep _ e l'));
simpl_inde_cmd_refl_head_output;
      Inde_cmd_refl
    | |- inde_cmd_refl ?c ((?p |lV~> ?l')::?Q) ?l =>
      apply (inde_cmd_refl_head c l (p |lV~> l') Q nil (subset_nil
            (A:=prod_eqType string_eqType _)) (@log_mapsto_only_dep _ p l'));
simpl_inde_cmd_refl_head_output;
      Inde_cmd_refl
    | |- inde_cmd_refl ?c ((?e |le~> ?l')::?Q) ?l =>
      apply (inde_cmd_refl_head c l (e |le~> l') Q (vars e) (vars_in_ts e) (@log_mapsto_e_only_dep _ e l'));
simpl_inde_cmd_refl_head_output;
      Inde_cmd_refl
    | |- inde_cmd_refl ?c ((!!(?P))::?Q) ?l =>
      eapply (inde_cmd_refl_head c l (!!(P)) Q nil (subset_nil
            (A:=prod_eqType string_eqType _)) (@sbang_only_dep P));
simpl_inde_cmd_refl_head_output;
      Inde_cmd_refl
    | |- inde_cmd_refl ?c ((sepexists ?P) :: ?Q) ?l =>
      eapply inde_cmd_refl_head_ex; intro; Inde_cmd_refl
    | |- inde_cmd_refl ?c ((?P \\// ?Q)::?R) ?l =>
      eapply inde_cmd_refl_head_or; Inde_cmd_refl
    | |- inde_cmd_refl ?c ((?P ** ?Q)::_) _ =>
      apply inde_cmd_refl_head_con; Inde_cmd_refl
    | |- inde_cmd_refl ?c (?P::_) _ =>
      try (rewrite /P; Inde_cmd_refl) (* NB: unfold P does not unfold (X a b c) when X is a Definition, rewrite / does *)

    | |- inde_cmd_refl ?c nil _ =>
      apply inde_cmd_refl_out
    | |- _ => idtac
  end
with simpl_inde_cmd_refl_head_output :=
match goal with
| |- inde_cmd_refl _ _ ?lst => rewrite [lst]/=
end.

Ltac Inde_cmd :=
  apply inde_cmd_refl_in; Inde_cmd_refl.

Lemma inde_cmd_nil c : inde_cmd c (icon nil). Proof. by []. Qed.

Lemma inde_cmd_cons c hd tl :
  inde_cmd c (icon (hd :: nil)) -> inde_cmd c (icon tl) -> inde_cmd c (icon (hd :: tl)).
Proof.
move=> Hh Ht /= s h str t pv str_mod; split.
  destruct tl.
  by apply Hh.
  case=> h1 h2 h1dh2 Hh1 Hh2.
  apply con_c => //.
  by apply Hh.
  by apply Ht.
destruct tl.
by apply Hh.
case=> h1 h2 h1dh2 Hh1 Hh2.
apply con_c => //.
by apply Hh in Hh1.
by apply Ht in Hh2.
  Qed.

Ltac Inde_cmd_NEW :=
  match goal with
    | |- inde_cmd ?c nil => apply inde_cmd_nil
    | |- inde_cmd ?c (icon (?P :: nil)) => Inde_cmd
    | |- inde_cmd ?c (icon (?P :: ?Q)) =>
      apply inde_cmd_cons;
        [ Inde_cmd
        | Inde_cmd_NEW ]
  end.

Lemma frame_rule_R_icon : forall c R, inde_cmd c (icon R) ->
  forall P Q, {{ icon P }} c {{ icon Q }} ->
    {{ icon ( P ++ R ) }} c {{ icon ( Q ++ R ) }}.
Proof.
move => c R H2 P Q H1.
rewrite iconE Sum_cat -!iconE.
apply (hoare_weak (icon Q ** icon R)).
  by rewrite [X in _ ===> X]iconE Sum_cat -!iconE.
by apply frame_rule_R.
Qed.

Lemma little_op_equiv_equiv : forall P Q, littleop.equiv P Q -> P <==> Q.
Proof. by []. Qed.

(* ?Q c'est la postcond du goal avant d'appliquer la tactique, say P' * R * Q
   icon ?P c'est la forme qu'on veut, say, P' ++ Q,R
   icon_POST c'est le icon de Q, i.e., P',Q,R
   new_l2 est une substitution qui transform P',R,Q en P',Q,R *)
Ltac Hoare_frame_postcond icon_POST new_l2 :=
  match goal with
    | |- icon ?P ===> ?Q =>
      let X := fresh in
      generalize (@Sum_rearrangement assert con assert_abelean icon_POST new_l2 Logic.eq_refl); intro X ;
      rewrite -2?iconE in X ;
      simpl icon in X ;
      apply (ent_trans _ _ _ (@equiv_imp2 _ _ (@little_op_equiv_equiv _ _ X))); by Ent_R_flat_match_icon
  end.
(* TODO: try to replace with Ent_L_permut *)

(* ?P originelle
   ?Q formatte pour la frame rule
   icon_PRE l'icon de P
   new_l2 une substitution du PRE originelle au Q formatte *)
Ltac Hoare_frame_precond icon_PRE new_l1 :=
  match goal with
    | |- ?P ===> icon ?Q =>
      let X := fresh in
      generalize (@Sum_rearrangement assert con assert_abelean icon_PRE new_l1 Logic.eq_refl); intro X ;
      rewrite -2?iconE in X ;
      simpl icon in X ;
      refine (ent_trans _ _ _ _ (@equiv_imp _ _ (@little_op_equiv_equiv _ _ X))); by Ent_L_flat_match_icon
  end.
(* TODO: try to replace with Ent_R_permut *)

Ltac Hoare_frame_idx_tmp i1 i2 :=
  match goal with
    | |- {{ ?P }} ?c {{ ?Q }} =>
      let C := fresh "frame_rule_set" in
      (set C := c);
      let icon_P := assert_to_seq P in (*TODO: superfluous*)
      let R_indices := eval simpl in (remove_indices icon_P i1) in
      let new_i1 := eval vm_compute in (cat i1 R_indices) in
      let new_P_for_frame_rule := eval simpl in
        (cat (map_indices emp icon_P i1) (map_indices emp icon_P R_indices)) in
      let icon_Q := assert_to_seq Q in (*TODO: superfluous*)
      let L_indices := eval vm_compute in (remove_indices icon_Q i2) in
      let new_i2 := eval vm_compute in (cat i2 L_indices) in
      let new_Q_for_frame_rule := eval simpl in
        (cat (map_indices emp icon_Q i2) (map_indices emp icon_Q L_indices)) in
      apply (hoare_conseq P (icon new_P_for_frame_rule) Q (icon new_Q_for_frame_rule)) ; [
         (by Hoare_frame_postcond icon_Q new_i2)
      |  (by Hoare_frame_precond icon_P new_i1)
      | let s1 := eval vm_compute in (size i1) in
        let s2 := eval vm_compute in (size i2) in
        rewrite - (cat_take_drop s1 new_P_for_frame_rule) ;
        rewrite - (cat_take_drop s2 new_Q_for_frame_rule) ;
        apply frame_rule_R_icon; simpl; [
          (now apply inde_nil) || (Inde_cmd; try (vm_compute; reflexivity))
        | unfold icon; simpl; unfold C ]
        ]
    end.

Ltac Hoare_frame l1 l2 :=
  match goal with
    | |- {{ ?P }} ?c {{ ?Q }} =>
      let icon_P := assert_to_seq P in
      let icon_P' := eval simpl in icon_P in
      let new_l1 := Find_indices l1 icon_P' in
      let icon_Q := assert_to_seq Q in
      let icon_Q' := eval simpl in icon_Q in
      let new_l2 := Find_indices l2 icon_Q' in
      Hoare_frame_idx_tmp new_l1 new_l2
  end.

Ltac Hoare_frame_remove' C l1 :=
  match goal with
| |- {{ icon ?P }} _ {{ icon ?Q }} =>
     let szq := eval vm_compute in (size Q - size l1) in
     let szp := eval vm_compute in (size P - size l1) in
     apply hoare_conseq with (Q' := icon (take szq Q ++ drop szq Q))
                             (P' := icon (take szp P ++ drop szp P)); [
        match goal with
          | |- _ ===> icon _ => rewrite -(cat_take_drop szq Q); apply ent_id
        end
    |   match goal with
          | |- icon _ ===> _ => rewrite -(cat_take_drop szp P); apply ent_id
        end
    | unfold icon; apply frame_rule_R_icon; simpl;
      [ (done || (Inde_cmd; try done ))
      | unfold icon; simpl; unfold C ] ]
end.

Ltac Hoare_frame_remove l1 :=
  match goal with
    | |- {{ _ }} ?c {{ _ }} =>
      let C := fresh "frame_rule_set" in
      (set C := c);
      Hoare_L_to_icon ; Hoare_R_to_icon ;
      let i1 := Hoare_R_icon_Find_indices l1 in
      Hoare_R_icon_put_in_back i1 ;
      let i2 := Hoare_L_icon_Find_indices l1 in
      Hoare_L_icon_put_in_back i2 ;
      Hoare_frame_remove' C l1
  end.

Ltac Ent_put_in_front_L_NEW lst :=
  match goal with |- ?P ===> _ => partition lst P ; move/equiv_imp ; apply entails_trans2 end.

Ltac Ent_put_in_front_R_NEW lst :=
  match goal with |-_ ===> ?Q => partition lst Q ; move/equiv_imp ; apply ent_trans end.

Ltac Ent_decompose_NEW l1 l2 :=
  Ent_put_in_front_L_NEW l1 ; Ent_put_in_front_R_NEW l2 ; apply monotony.

Ltac Hoare_R_put_in_front_NEW lst :=
  match goal with
    | |- {{ _ }} _ {{ ?Q }} =>
      partition lst Q ; let H := fresh in move/equiv_imp2 => H ; apply (hoare_weak _ _ _ _ H) ; clear H
  end.

Ltac Hoare_L_put_in_front_NEW lst :=
  match goal with
    | |- {{ ?P }} _ {{ _ }} =>
      partition lst P ; let H := fresh in move/equiv_imp => H ; apply (hoare_stren _ _ _ _ H) ; clear H
  end.

Ltac Hoare_frame_remove_NEW l1 :=
  match goal with
    | |- {{ _ }} ?c {{ _ }} =>
      let C := fresh "frame_rule_set" in
      (set C := c);
      Hoare_R_put_in_front_NEW l1 ;
      Hoare_L_put_in_front_NEW l1;
      apply frame_rule_L ; unfold C; [ |
      apply inde_cmd_icon ; Inde_cmd ]; last first
  end.

Ltac Hoare_frame_remove_idx l1 l2 :=
  match goal with
    | |- {{ _ }} ?c {{ _ }} =>
      let C := fresh "frame_rule_set" in
      (set C := c);
      eapply hoare_conseq; [
        Ent_R_to_icon;
        Ent_R_icon_put_in_back l2;
        match goal with
          | |- _ ===> icon ?P =>
            let sz := eval vm_compute in (size P - size l2) in
              rewrite -(cat_take_drop sz P); apply ent_id
        end
      | Ent_L_to_icon;
        Ent_LR_icon_put_in_back l1;
        match goal with
          | |- icon ?P ===>  _ =>
            let sz := eval vm_compute in (size P - size l1) in
              rewrite -(cat_take_drop sz P); apply ent_id
        end
      | rewrite iconE; eapply frame_rule_R_icon; simpl;
        [ (done || (Inde_cmd; try done ))
        | unfold icon; simpl; unfold C ] ]
  end.

Ltac Rewrite_Precond H :=
  eapply triple_morphism2; [
    (red; rewrite -> H ; first by apply ent_id)
  | apply Logic.eq_refl
  | apply ent_id
  | idtac].

Ltac Rewrite_Postcond H :=
  eapply triple_morphism2; [
    apply ent_id
  | apply Logic.eq_refl
  | (rewrite <- H ; first by apply ent_id)
  | idtac].

Ltac Ent_R_conC :=
  match goal with
    | |- _ ===> ?P ** ?Q =>
      eapply ent_trans; last by apply (equiv_imp2 _ _ (conC P Q))
  end.

Ltac Ent_R_conA' :=
  match goal with
    | |- _ ===> ?P ** (?Q ** ?R) =>
      eapply ent_trans; last by apply (equiv_imp2 _ _ (conA P Q R))
  end.

Ltac Ent_L_conA :=
  match goal with
    | |- ?P ** (?Q ** ?R) ===> _ =>
      eapply ent_trans; first by apply (equiv_imp _ _ (conA P Q R))
  end.

Ltac Ent_L_conA' :=
  match goal with
    | |- (?P ** ?Q) ** ?R ===> _ =>
      eapply ent_trans; first by apply (equiv_imp2 _ _ (conA P Q R))
  end.

Ltac fmt :=
match goal with
| |- ?P1 ** ?P2 ===> ?P1 ** _ => apply monotony_L; fmt
| |- ?P1 ** ?P2 ===> _ ** ?P2 => apply monotony_R; fmt
| |- ?P1 ** ?P2 ===> ?P2 => apply monotony_R1
| |- ?P1 ** ?P2 ===> ?P1 => apply monotony_L1
| |- (?P1 ** ?P2) ** ?P3 ===> _  => Ent_L_conA' ; fmt
| |- ?P1 ** ?P2 ===> _  => rewrite (conC P1); fmt
| |- _ => idtac
end.

Ltac Hoare_L_contract_bbang H :=
  let i := Hoare_L_Find_index H in
  match goal with
    | |- {{ ?P }} _ {{ _ }} =>
      let P' := assert_to_seq P in
      let P'' := eval simpl in (seq_ext.idel i P') in
      apply (hoare_stren (icon P'')); [
        rewrite iconE /=; fmt ; apply ent_bbang_contract
      | rewrite iconE /= (* NB(rei): failed with 8.6.1 [in X in {{ X }} _ {{ _ }}]/=*) ]
  end.

Ltac Ent_L_contract_bbang i :=
  match i with
    | O => match goal with
               | |- _ ** _ ===> _ => apply ent_L_bbang_con
               | |- _ ===> _ => apply ent_L_bbang
           end
    | S _ =>
      match goal with
        | |- ?P ===> _ =>
          let P' := assert_to_seq P in
          let a := eval simpl in (nth emp P' i) in
          rewrite -> (ent_bbang_contract2 a Logic.eq_refl); (rewrite coneP || rewrite conPe || idtac)
      end
  end.

Ltac Hoare_seq_ext A :=
  match goal with
    | |- {{ ?P }} _; _ {{ _}} => apply hoare_seq with (A ** P)
  end.

Ltac Assert_replace P src des :=
  let P_seq := assert_to_seq P in
  let src_indices := Find_indices src P_seq in
  let P'_indices := eval simpl in (remove_indices P_seq src_indices) in
  let P'_seq := eval simpl in (map (nth emp P_seq) P'_indices) in
  eval simpl in (@Sum _ con assert_abelean (P'_seq ++ des)).

Ltac Hoare_seq_replace l1 l2 :=
  match goal with
    | |- {{ ?P }} _; _ {{ _ }} => let R := Assert_replace P l1 l2 in apply hoare_seq with R
  end.

Ltac Assert_replace1 P src des :=
  let P_seq := assert_to_seq P in
  let src_idx := Find_index src P_seq in
  let P'_seq := eval simpl in (seq_replace P_seq des src_idx) in
  eval simpl in (@littleop.Sum _ con assert_abelean P'_seq).

Ltac Hoare_seq_replace1 l1 l2 :=
  match goal with
    | |- {{ ?P }} _ ; _ {{ _ }} => let R := Assert_replace1 P l1 l2 in apply hoare_seq with R
  end.

Local Open Scope C_cmd_scope.

Ltac Ent_L_stren A :=
  match goal with
    | |- ?P ===> _ => apply (ent_trans (A ** P))
  end.

Ltac Hoare_L_stren A :=
  match goal with
    | |- {{ ?P }} ?c1 {{ ?Q }} => apply (hoare_stren (A ** P))
  end.

Ltac Ent_L_dup1 B :=
  match goal with
    | |- _ ===> _ =>
      match goal with
        | |- context ctxt [ B ] =>
          let x := context ctxt [ B ** B ] in
          match x with
            | ?P ===> ?Q =>
              apply (ent_trans P);
                [ Ent_monotony0_new (solve [ apply (equiv_imp _ _ (bbang_dup2 B Logic.eq_refl)) |
                                       apply (equiv_imp _ _ (sbang_dup2 B Logic.eq_refl)) ] )
                | idtac ]
          end
      end
  end.

Ltac Ent_L_dup l :=
  match l with
    | nil => idtac
    | ?hd :: ?tl => Ent_L_dup1 hd; Ent_L_dup tl
  end.

Ltac Ent_L_stren_by P l :=
  Ent_L_stren P; [ Ent_L_dup l; Ent_monotony | idtac].

Ltac Hoare_L_dup lst :=
  match goal with
      | |- {{ ?P }} ?c {{ ?Q }} =>
        eapply hoare_stren;
          [ (Ent_L_dup lst; by apply ent_id)
          | idtac ]
  end.

Ltac Hoare_L_stren_by P l :=
  Hoare_L_stren P; [ Ent_L_dup l; Ent_monotony | idtac ].

(** contradiction *)

Lemma ent_R_F_icon P P' : icon P' ===> FF -> icon ( P' ++ P ) ===> FF.
Proof.
move => H.
eapply ent_trans; last by apply H.
rewrite iconE /= Sum_cat => s h.
by case => h1 h2 h1dh2 /H.
Qed.

Ltac Ent_L_contradict_idx lst :=
  Ent_L_to_icon ;
  Ent_L_icon_put_in_front lst; refine (ent_trans FF _ _ _ (ent_L_F _)) ;
  let sz := eval vm_compute in (size lst) in
  match goal with
  | |- icon ?P ===> _ =>
      rewrite -(cat_take_drop sz P) ; apply ent_R_F_icon; rewrite iconE /=;
      solve [ by rewrite bbang_contradict |
              by rewrite bbang_contradict' ]
  end.

Ltac Find_inverse_bbang b l :=
  match l with
    | nil => fail "no inverse"
    | !b(\~b b)::_ => constr: (0)
    | _::?tl =>
      let index := Find_inverse_bbang b tl in
        constr: (index.+1)
  end.

Ltac Unfold_names lst :=
  match lst with
    | nil => idtac
    | ?hd::?tl =>
      unfold hd; Unfold_names tl
  end.

Ltac Ent_L_contradict names :=
  Ent_L_to_icon ;
  let l := Ent_L_icon_Find_indices names in
  Ent_L_icon_put_in_front l; refine (ent_trans FF _ _ _ (ent_L_F _)) ;
  let sz := eval vm_compute in (size names) in
  match goal with
  | |- icon ?P ===> _ =>
        rewrite -(cat_take_drop sz P) ; apply ent_R_F_icon; rewrite iconE /=;
        Unfold_names names;
          solve [ by rewrite bbang_contradict |
                  by rewrite bbang_contradict' ]
  end.

Ltac Hoare_L_contradict lst :=
  apply (hoare_stren FF); [ Ent_L_contradict_idx lst | by apply hoare_L_F].

Ltac Ent_LR_subst_inde :=
  rewrite wp_assign_inde; [idtac |
                           match goal with
                             | |- inde_cmd ?c ?P =>
                               apply inde_cmd_icon;
                               Inde_cmd; try done
                           end
                          ].

Ltac Hoare_stren_pull_out l H :=
  match goal with
    | |- {{ _ }} ?c {{ _ }} =>
      apply hoare_stren_pull_out' with (P' := l) (a := H); [
          (* first subgoal should be solvable by Ent_monotony *) Ent_monotony |
          (* second subgoal is up to the user *) idtac |
          (* last subgoal is the continuation with pulled out information *) idtac
        ]
  end.

Ltac Simpl_subst_exp :=
  match goal with
    |- context ctxt [(subst_exp ?var ?val ?e)] =>
    rewrite [(subst_exp var val e)]/=
  end.

Ltac Eq_rect :=
  match goal with
    |- context ctxt [@eq_rect ?A ?x ?P ?Px ?y ?h] =>
    rewrite -(@Eqdep.Eq_rect_eq.eq_rect_eq _ x P Px h)
  end.

Ltac Bop_r_eq_eq_to_canonical :=
  match goal with
      |- context ctxt [bop_r ?sigma ?t eq_e ?lhs ?rhs] =>
      rewrite -/(lhs \= rhs)
  end.

Ltac Eq_p_to_canonical :=
  match goal with
      |- context ctxt [eq_p ?sigma ?t ?lhs ?rhs] =>
      rewrite -/(lhs \= rhs)
  end.

Ltac Back_to_canonical :=
  (try Bop_r_eq_eq_to_canonical) ;
  (try Eq_p_to_canonical).

Ltac Simpl_subst_bexp :=
  match goal with
    |- context ctxt [`! (subst_bexp ?var ?H ?val ?e)] =>
    rewrite [`! (subst_bexp var H val e)]/=;
    Back_to_canonical
  end.

Ltac Ent_R_subst_apply :=
  match goal with
    | |- _ ===> ?rhs =>
      match rhs with
          | context ctxt [wp_assign ?Hstr ?val ?HH] =>
            match HH with
              | (`! ?e) =>
        let H := fresh in
        generalize (equiv_imp2 _ _ (@wp_assign_bbang _ _ Hstr val e)); intro H ;
        match goal with
          | H : ?Hsubst ===> _ |- _ =>
            let new_goal := context ctxt [ Hsubst ] in
            easy_Ent_monotony_R new_goal H ;
              Simpl_subst_bexp ;
              (try Eq_rect)
        end
          | (?e |---> ?s ) =>
        let H := fresh in
        generalize (equiv_imp2 _ _ (@wp_assign_mapstos_fit _ _ Hstr val _ s e)); intro H ;
        match goal with
          | H : ?Hsubst ===> _ |- _ =>
            let new_goal := context ctxt [ Hsubst ] in
            easy_Ent_monotony_R new_goal H ;
              (try Simpl_subst_exp; try Eq_rect)
        end
          | (?e |--> ?s ) =>
        let H := fresh in
        generalize (equiv_imp2 _ _ (@wp_assign_mapstos _ _ Hstr val _ s e)); intro H ;
        match goal with
          | H : ?Hsubst ===> _ |- _ =>
            let new_goal := context ctxt [ Hsubst ] in
            easy_Ent_monotony_R new_goal H ;
              (try Simpl_subst_exp; try Eq_rect)
        end
      | (?e' |le~> ?val') =>
        let H := fresh in
        generalize (equiv_imp2 _ _ (@wp_assign_mapsto_le _ _ Hstr val _ e' val')); intro H ;
        match goal with
          | H : ?Hsubst ===> _ |- _ =>
            let new_goal := context ctxt [ Hsubst ] in
            easy_Ent_monotony_R new_goal H ;
              (try Simpl_subst_exp)
        end
      | (?e' |lV~> ?val') =>
        let H := fresh in
        generalize (equiv_imp2 _ _ (@wp_assign_mapsto_lV _ _ Hstr val _ e' val')); intro H ;
        match goal with
          | H : ?Hsubst ===> _ |- _ =>
            let new_goal := context ctxt [ Hsubst ] in
            easy_Ent_monotony_R new_goal H
        end
      | (sepexists ?P) =>
        let H := fresh in
        generalize (equiv_imp2 _ _ (@wp_assign_ex _ _ Hstr val _ P)); intro H ;
        match goal with
          | H : ?Hsubst ===> _ |- _ =>
            let new_goal := context ctxt [ Hsubst ] in
            easy_Ent_monotony_R new_goal H
        end
      | (sbang ?P) =>
        let H := fresh in
        generalize (equiv_imp2 _ _ (@wp_assign_sbang _ _ Hstr val P)); intro H ;
        match goal with
          | H : ?Hsubst ===> _ |- _ =>
            let new_goal := context ctxt [ Hsubst ] in
            easy_Ent_monotony_R new_goal H
        end
      | TT =>
        let H := fresh in
        generalize (equiv_imp2 _ _ (@wp_assign_T _ _ Hstr val)); intro H ;
        match goal with
          | H : ?Hsubst ===> _ |- _ =>
            let new_goal := context ctxt [ Hsubst ] in
            easy_Ent_monotony_R new_goal H
        end
      | FF =>
        let H := fresh in
        generalize (equiv_imp2 _ _ (@wp_assign_F _ _ Hstr val)); intro H ;
        match goal with
          | H : ?Hsubst ===> _ |- _ =>
            let new_goal := context ctxt [ Hsubst ] in
            easy_Ent_monotony_R new_goal H
        end
      | ?H' =>
        unfold H'; Ent_R_subst_apply
    end
end
end.

Section testme.

Definition str := "mystring"%string.

Variables (t : integral) (str_t : env_get str sigma = |_ ityp: t _|).

Definition P := `! \b var_e sigma str _ str_t \= var_e sigma str _ str_t.
Definition Q := `! \b var_e sigma str _ str_t \!= var_e sigma str _ str_t.

Goal (emp ===> Q ** wp_assign str_t [ pv0 ]c P).
Ent_R_subst_apply.
Abort.

End testme.

Ltac Ent_L_subst_apply :=
  match goal with
    | |- ?lhs ===> _ =>
      match lhs with
        | context ctxt [wp_assign ?Hstr ?val ?HH] =>
          match HH with
        | (`! ?e) =>
          let H := fresh in
          generalize (equiv_imp _ _ (@wp_assign_bbang _ _ Hstr val e)); intro H ;
          match goal with
            | H : _ ===> ?Hsubst |- _ =>
              let new_goal := context ctxt [ Hsubst ] in
              easy_Ent_monotony_L new_goal H ;
                Simpl_subst_bexp ;
                (try Eq_rect)
          end
        | (?e |---> ?s ) =>
          let H := fresh in
          generalize (equiv_imp _ _ (@wp_assign_mapstos_fit _ _ Hstr val _ s e)); intro H ;
          match goal with
            | H : _ ===> ?Hsubst |- _ =>
              let new_goal := context ctxt [ Hsubst ] in
              easy_Ent_monotony_L new_goal H ;
                (try Simpl_subst_exp; try Eq_rect)
          end
        | (?e |--> ?s ) =>
          let H := fresh in
          generalize (equiv_imp _ _ (@wp_assign_mapstos _ _ Hstr val _ s e)); intro H ;
          match goal with
            | H : _ ===> ?Hsubst |- _ =>
              let new_goal := context ctxt [ Hsubst ] in
              easy_Ent_monotony_L new_goal H ;
                (try Simpl_subst_exp; try Eq_rect)
          end
        | (?e' |le~> ?val') =>
          let H := fresh in
          generalize (equiv_imp _ _ (@wp_assign_mapsto_le _ _ Hstr val _ e' val')); intro H ;
          match goal with
            | H : _ ===> ?Hsubst |- _ =>
              let new_goal := context ctxt [ Hsubst ] in
              easy_Ent_monotony_L new_goal H ;
                try Simpl_subst_exp
          end
        | (?e' |lV~> ?val') =>
          let H := fresh in
          generalize (equiv_imp _ _ (@wp_assign_mapsto_lV _ _ Hstr val _ e' val')); intro H ;
          match goal with
            | H : _ ===> ?Hsubst |- _ =>
              let new_goal := context ctxt [ Hsubst ] in
              easy_Ent_monotony_L new_goal H
          end
        | (sepexists ?P) =>
          let H := fresh in
          generalize (equiv_imp _ _ (@wp_assign_ex _ _ Hstr val _ P)); intro H ;
          match goal with
            | H : _ ===> ?Hsubst |- _ =>
              let new_goal := context ctxt [ Hsubst ] in
              easy_Ent_monotony_L new_goal H
          end
        | (sbang ?P) =>
          let H := fresh in
          generalize (equiv_imp _ _ (@wp_assign_sbang _ _ Hstr val P)); intro H ;
          match goal with
            | H : _ ===> ?Hsubst |- _ =>
              let new_goal := context ctxt [ Hsubst ] in
              easy_Ent_monotony_L new_goal H
          end
        | TT =>
          let H := fresh in
          generalize (equiv_imp _ _ (@wp_assign_T _ _ Hstr val)); intro H ;
          match goal with
            | H : _ ===> ?Hsubst |- _ =>
              let new_goal := context ctxt [ Hsubst ] in
              easy_Ent_monotony_L new_goal H
          end
        | FF =>
          let H := fresh in
          generalize (equiv_imp _ _ (@wp_assign_F _ _ Hstr val)); intro H ;
          match goal with
            | H : _ ===> ?Hsubst |- _ =>
              let new_goal := context ctxt [ Hsubst ] in
              easy_Ent_monotony_L new_goal H
          end
        | ?H' =>
          unfold H'; Ent_L_subst_apply
      end
end
end.

Ltac Ent_LR_subst_apply := match goal with
| |- ?P ===> ?Q =>
  first [Ent_L_subst_apply | Ent_R_subst_apply]
end.

Ltac Ent_L_subst_apply_rewrite_bbang Hstr val e :=
          let H := fresh in
          generalize (equiv_imp _ _ (@wp_assign_bbang _ _ Hstr val e)) ; intro H ;
          match goal with
            | H : _ ===> ?Hsubst |- ?lhs ===> _ =>
              match lhs with
                | context ctxt [wp_assign Hstr val (`! e)] =>
                  let new_goal := context ctxt [ Hsubst ] in
                  easy_Ent_monotony_L new_goal H ;
                    Simpl_subst_bexp ;
                    (try Eq_rect)
              end
          end.

Ltac Ent_L_subst_apply_bbang_occ_rec n curr_lhs :=
  match curr_lhs with
    | context ctxt [wp_assign ?Hstr ?val (`! ?e)] =>
      match n with
        | O => Ent_L_subst_apply_rewrite_bbang Hstr val e
        | S ?n' =>
          let new_lhs := context ctxt [TT] in
          Ent_L_subst_apply_bbang_occ_rec n' new_lhs
      end
  end.

Ltac Ent_L_subst_apply_bbang_occ n :=
  match goal with
    | |- ?lhs ===> _ =>
      Ent_L_subst_apply_bbang_occ_rec n lhs
  end.

Local Open Scope machine_int_scope.

Lemma leqnSSn n : n <= n.+2.
Proof. by elim: n. Qed.

Lemma mod_1_even_gen (e : exp _ (ityp: sint)) n (Hn : n <= 30) :
  `! \b [ 0 ]sc \<= e **
  `! \b e \<= [2 ^^ n.+1 - 1]sc **
  `! \b e \% 1 \= [ 0 ]sc ===>
  (sepex k, `! \b e \= [ cast_subnK (leq_trans Hn (leqnSSn _))
                         (zext (32 - n) (k : int n) `<< 1) ]pc).
Proof.
move=> s h [] h1 h2 _.
case=> H1. rewrite /emp => ->.
case=> h21 h22 _.
case=> H2. rewrite /emp => ->.
case=> H3. rewrite /emp => ->.
move: H1 H2 H3.
Transparent eval beval.
rewrite [succn n]lock.
simpl.
move He : ( [ e ]_s) => [he Hhe].
rewrite !i8_of_i32K.
set H' := eq_ind_r _ _ _.
have -> : H' = Hhe by apply eq_irrelevance.
simpl.
rewrite !i8_of_i32K.
case: ifP; last by rewrite is_zero_0.
rewrite not_is_zero_1.
move=> H1 _.
case: ifP; last by rewrite is_zero_0.
rewrite not_is_zero_1.
move=> H2 _.
case: ifP; last by rewrite is_zero_0.
rewrite not_is_zero_1.
move/eqP/s2Z_inj => H _.
rewrite Z2s_Z2u_k // in H.
set lhs := _ `% 32 in H.
have {H}H : u2Z lhs = u2Z zero32 by rewrite H.
rewrite /lhs {lhs} in H.
rewrite u2Z_rem' in H; last by apply (@ltZ_trans (2 ^^ 1)) => //; exact: max_u2Z.
exists ((i32<=i8 he Hhe `>> 1) `% n).
split => //.
simpl.
rewrite He.
rewrite -/H'.
set H'' := eq_ind_r _ _ _.
rewrite i8_of_i32K.
case: ifP; first by rewrite not_is_zero_1.
have -> : H' = Hhe by apply eq_irrelevance.
rewrite is_zero_0 /=.
move=> <-.
apply/eqP.
congr (Z<=s).
rewrite (@cast_shl 32 n (i32<=i8 he Hhe `>> 1 `% n) (leq_trans Hn (leqnSSn _)) 1); last first.
  by rewrite addn1 (leq_ltn_trans Hn).
have -> : cast_subnK (leq_trans Hn (leqnSSn _))
  (zext (32 - n) (i32<=i8 he Hhe `>> 1 `% n)) = i32<=i8 he Hhe `>> 1.
  apply u2Z_inj.
  rewrite u2Z_cast.
  rewrite u2Z_zext //.
  rewrite u2Z_rem' //.
  rewrite u2Z_shrl' //.
  rewrite -s2Z_u2Z_pos; last first.
    rewrite Z2sK // in H1.
    by move/leZP in H1.
  apply Z.div_lt_upper_bound => //.
  move/leZP in H2.
  rewrite Z2sK // in H2; last first.
    rewrite -lock.
    split.
      apply (@leZ_trans Z0) => //.
      apply Zle_minus_1; exact: expZ_gt0.
    apply (@leZ_ltZ_trans (2 ^^ 30.+1 - 1)%Z) => //.
    apply/leZ_sub2r/leZP; by rewrite Zpower_2_le.
  rewrite -lock ZpowerS in H2.
  rewrite [2 ^^ 1]/=; omega.
  rewrite shrl_shl //.
  apply u2Z_inj.
  rewrite H.
  by rewrite /zero32 !Z2uK.
Opaque eval beval.
by rewrite !hp.unioneh.
Qed.

Lemma mod_1_even_nat_gen str H n (Hn : n <= 30) :
  `! \b [ 0 ]sc \<= var_e _ str _ H **
  `! \b var_e _ str (ityp: sint) H \<= [ 2 ^^ n.+1 - 1 ]sc **
    `! \b var_e _ str _ H \% 1 \= [ 0 ]sc ===>
  (sepex k', !!(Z<=nat k' * 2 < 2 ^^ n.+1)%Z **
             `! \b var_e _ str _ H \= [ Z<=nat k' * 2 ]sc ).
Proof.
set tmp := \b _ .
set tmp2 := \b var_e _ _ _ _ \<= _ .
apply (ent_trans (`! tmp ** `! tmp2 ** sepex k,
  `! \b var_e _ str _ H \= [ cast_subnK (leq_trans Hn (leqnSSn _))
                                (zext (32 - n) (k : int n) `<< 1) ]pc)).
  rewrite -> (@bbang_dup2 tmp _ Logic.eq_refl) at 1.
  rewrite -> (@bbang_dup2 tmp2 _ Logic.eq_refl) at 1.
  Ent_monotony.
  by apply mod_1_even_gen.
rewrite [expZ]lock.
Ent_L_ex_n 0 k.
Ent_R_ex_n 0 (nat<=u k).
rewrite /tmp /tmp2 {tmp tmp2} [succn n]lock.
Ent_LR_rewrite_eq_e 0.
do 2 rewrite wp_assign_bbang /= /eq_rect_r /= string_decxx -!Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
Ent_R_subst_con_distr.
Ent_LR_subst_inde.
rewrite wp_assign_bbang /= /eq_rect_r /= string_decxx /= -!Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
rewrite /u2nat Z_of_nat_Zabs_nat; last by apply min_u2Z.
Bbang2sbang.
move=> s h.
case=> h1 h2 _.
case=> H1. rewrite /emp. move=> ?; subst h1.
case=> H2. rewrite /emp. move=> ?; subst h2.
have K : (Z<=s (zext (32 - n) k `<< 1) = Z<=u k * 2)%Z.
  rewrite (@s2Z_shl n) //; last first.
    rewrite s2Z_zext //.
    split.
      apply (@leZ_trans Z0).
        rewrite leZ_oppl oppZ0; exact: expZ_ge0.
      exact: min_u2Z.
    exact: max_u2Z.
    rewrite -(ltn_add2r n) add0n subnK.
      by apply leq_ltn_trans with 30.
    by apply (leq_trans Hn).
  rewrite subnK; last by rewrite (leq_trans Hn).
  rewrite addnC addn1 ltnS.
  by apply leq_ltn_trans with 30.
  rewrite s2Z_zext // -(ltn_add2r n) add0n subnK.
    by apply leq_ltn_trans with 30.
  exact: (leq_trans Hn).
Transparent eval beval.
rewrite -(ground_bexp_sem (store0 sigma)) in H2.
apply bop_re_le_Zle in H2.
rewrite /= !phy_of_si32K Z2sK // in H2; last first.
  split.
    apply (@leZ_trans Z0) => //.
    rewrite -lock ZpowerS.
    move: (expZ_gt0 n) => ?; omega.
  rewrite -lock.
  move: (Hn).
  rewrite -ltnS -Zpower_2_le => /leZP ?; omega.
rewrite -(ground_bexp_sem (store0 sigma)) in H1.
apply bop_re_le_Zle in H1.
rewrite /= !phy_of_si32K Z2sK // in H1.
apply con_c.
- by apply hp.disjeh.
- split=> //.
  rewrite -K -lock /=.
  apply: leZ_ltZ_trans.
    rewrite s2Z_cast in H2; by apply H2.
  rewrite -lock; omega.
- split => //.
  rewrite -K -(ground_bexp_sem (store0 sigma)) beval_eq_e_eq /=.
  apply/eqP.
  apply si32_of_phy_inj.
  rewrite phy_of_si32K.
  apply s2Z_inj.
  rewrite s2Z_cast phy_of_si32K Z2sK //.
  split.
    apply (@leZ_trans Z0) => //.
    rewrite (@s2Z_shl 30); last 2 first.
      by rewrite subnK // (leq_trans Hn).
      rewrite s2Z_zext; last first.
        rewrite -(ltn_add2r n) add0n subnK.
        by rewrite (@ltn_trans 31).
        by rewrite (leq_trans Hn).
      split.
        apply (@leZ_trans Z0) => //; by apply min_u2Z.
      apply: ltZ_leZ_trans; first by apply max_u2Z.
      by apply/leZP; rewrite Zpower_2_le.
    rewrite s2Z_zext; last first.
      rewrite -(ltn_add2r n) add0n subnK.
      by rewrite (@ltn_trans 31).
      by rewrite (leq_trans Hn).
    apply mulZ_ge0 => //; by apply min_u2Z.
  apply: ltZ_leZ_trans; first by apply max_s2Z.
  by rewrite subnK // (leq_trans Hn).
Opaque eval beval.
Qed.

Local Close Scope machine_int_scope.

End C_Tactics_f.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Min.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import ZArith_ext seq_ext machine_int uniq_tac.
Import MachineInt.
Require Import mips_bipl.

Import assert_m.

Local Open Scope heap_scope.
Local Open Scope mips_assert_scope.
Local Open Scope machine_int_scope.

Ltac Compose_sepcon id1 id2:=
  exists id1, id2; split;
    [map_tac_m.Disj | (split; [ map_tac_m.Equal | split; idtac])].

(* TODO: move to seq_ext? *)
Ltac Decompose_list_32 lst u lst1 lst2 :=
  lapply (@list_split (int 32) zero32 (size lst) lst (refl_equal (size lst)) u);
    [let X := fresh in
      (intro X;
	let Y := fresh in
	  (inversion_clear X as [lst1 Y];
	    let Z := fresh in
	      let U := fresh in
		(inversion_clear Y as [Z U];
		  inversion_clear U as [lst2]))) | idtac].

(* NB: the module is open, remove prefixes? *)
Ltac normalize_left :=
  match goal with
    | |- ((?P1 ** ?P2) ** ?P3) ?s ?h -> _ =>
      rewrite (assert_m.conAE P2 P1 P3); normalize_left
    | |- context [ ((?P1 ** ?P2) ** ?P3) ] =>
      rewrite (assert_m.conAE P2 P1 P3); normalize_left
    | |- _ => idtac
  end.

Ltac normalize_right :=
  match goal with
    | |- _ -> ((?P1 ** ?P2) ** ?P3) ?s ?h  =>
      rewrite (assert_m.conAE P2 P1 P3); normalize_right
    | |- context [ ((?P1 ** ?P2) ** ?P3) ] =>
      rewrite (assert_m.conAE P2 P1 P3); normalize_right
    | |- _ => idtac
  end.

Ltac rotate_left :=
  match goal with
    | |- (?P ** ?Q) ?s ?h  -> _ => rewrite (assert_m.conCE P Q)
    | |- _ => idtac
  end.

Ltac rotate_right :=
  match goal with
    | |- _ -> (?P ** ?Q) ?s ?h => rewrite (assert_m.conCE P Q)
    | |- _ => idtac
  end.

Ltac ConAE P :=
  match P with
    | (?Q ** ?R) ** ?S => rewrite conAE; ConAE (Q ** (R ** S))
    | _ => idtac
  end.

Ltac ApplyToHyp T H :=
  move: H;
  match goal with | |- ?P ?s ?h -> _ => T P end;
  move => H.

Ltac ApplyToGoal T := match goal with | |- ?P ?s ?h => T P end.

Ltac Rotate H := ApplyToHyp ConAE H; rewrite conCE in H; ApplyToHyp ConAE H.

Ltac RotateGoal := ApplyToGoal ConAE; rewrite conCE; ApplyToGoal ConAE.

Ltac monotony_or_rotate_left n :=
  match n with
    | O => rotate_right; normalize_right
    | S ?k =>
      match goal with
	| |- (?P ** _) ?s ?h -> (?P ** _) ?s ?h =>
	  apply monotony; [solve [auto] | intro; idtac]
	| |- (_ ** _) ?s ?h -> (_ ** _) ?s ?h =>
	  rotate_left; normalize_left; monotony_or_rotate_left k
      end
  end.

Ltac count_sepcons e :=
  match e with
    (?e1 ** ?e2) =>
    let tmp1 := count_sepcons e1 in
      let tmp2 := count_sepcons e2 in
	eval compute in (tmp1 + tmp2 + 1)%nat
    | _ => O
  end.

Ltac count_conjuncts e := let tmp := count_sepcons e in
  eval compute in (tmp + 1)%nat.

Ltac try_monotony_and_rotate_right n :=
  match n with
    O => idtac
    | S ?k =>
      match goal with
	| |- (?e1 ** ?e2) ?s ?h -> (_ ** _) ?s ?h =>
	  let left_conjuncts := count_conjuncts (e1 ** e2) in
	    monotony_or_rotate_left left_conjuncts;
	    try_monotony_and_rotate_right k
	| |- (_ |--> _) ?s ?h -> (_ |--> _) ?s ?h =>
	  intros; auto
	| |- ?P ?s ?h -> ?P ?s ?h  => solve [auto]
        | |- _ => idtac
      end
  end.

Ltac assoc_comm H :=
  generalize H; clear H;
    match goal with
      | |- (_ ** _) ?s ?h -> (?e1 ** ?e2) ?s ?h =>
	normalize_right;
	normalize_left;
	let right_conjuncts := count_conjuncts (e1 ** e2) in
	  try_monotony_and_rotate_right right_conjuncts
    end;
    intro H.

Ltac rotate := apply: uniq_rotate'; simpl cat.
Ltac trash := apply: uniq_head'.

Ltac Uniq_uniq_old' :=
  match goal with
    | [ |- is_true (uniq (?lst)) -> is_true (uniq (?lst)) ] => done
    | [ |- is_true (uniq (?hd::?tl)) -> is_true (uniq (?hd::?tl')) ] =>
      apply: uniq_head; [Uniq_not_In | Uniq_uniq_old']
    | [ |- is_true (uniq (?hd::?tl)) -> is_true (uniq (?lst)) ] =>
      match In_list hd lst with
        | true => rotate; Uniq_uniq_old'
        | _ => trash; Uniq_uniq_old'
      end
    | _ => fail "Uniq_uniq_old'"
  end.

Ltac Uniq_uniq_old :=
  match goal with
    | [ H : is_true (uniq ?lst) |- is_true (uniq ?lst') ] =>
      move: (H); Uniq_uniq_old'
  end.

Module test.

Axiom r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 : reg.

Goal uniq (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: nil) ->
  uniq (r0 :: r1 :: r3 :: r2 :: nil).
intros.

move: H.
  match goal with
    | |- is_true (uniq ?l) -> is_true (uniq ?k)=>
      let inj := seq_ext.compute_list_injection l k in
(*      let perm := eval compute in
          (remove_idx l (fun x => negb (inb beq_nat x inj)) O) in
      let Htmp := fresh in
      move=> Htmp ;

      move: (nodup_remove_idx _ _ Htmp
        (fun x => negb (inb beq_nat x inj)) O);
      rewrite [remove_idx _ _ _]/= {Htmp}*)
        idtac inj
  end.
(*intro; Uniq_uniq r0.*)
intro; Uniq_uniq_old.
Qed.

Goal uniq (r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: r7 :: r8 :: r9 :: r10 :: r11 :: r12 :: r13 :: r14 :: r15 :: r16 :: nil) ->
  uniq (r4 :: r5 :: r9 :: r10 :: r8 :: r7 :: r12 :: r11 :: nil).
intros.
(*Uniq_uniq r0.*)
Uniq_uniq_old.
Qed.

End test.

Ltac Disj_cons_L :=
  match goal with
    | |- seq_ext.disj (?hd :: nil) ?lst' =>
      apply seq_ext.disj_cons_L ;
        [ apply seq_ext.disj_nil_L | Uniq_not_In ]
  end.

Ltac Disj_cons :=
  match goal with
    | |- seq_ext.disj ?lst ?lst' =>
      rewrite [lst]/=; Disj_cons_L
  end.

Ltac Inde_mapsto_tac :=
  match goal with
    | |- inde ?lst (?exp |~> expr_m.int_e ?exp') =>
      rewrite [lst]/=;
      apply inde_mapsto_int_e;
      Disj_cons
  end.

Ltac Inde :=
  match goal with
    | |- inde ?L (?P ** ?Q) => apply inde_sep_con; Inde
    | |- inde ?L (?P //\\ ?Q) => apply inde_sep_and; Inde
    | |- inde ?L (expr_m.var_e ?V |--> ?L') => apply inde_mapstos_var_e; Uniq_not_In
    | |- inde ?L (expr_m.int_e ?V |--> ?L') => apply inde_mapstos_int_e
    | |- inde ?L (?e |--> ?L') => apply inde_mapstos; rewrite [expr_m.vars _]/=; by Disj_uniq r0
    | |- inde ?L TT => apply inde_TT
    | |- inde ?lst (?exp |~> ?exp') => Inde_mapsto_tac
    | |- inde ?L (fun _ _ => _ /\ _) => apply inde_and; Inde
    | |- inde ?L (! (fun _ : store.t => _)) => apply inde_bang; Inde
    | |- inde ?L (fun _ _ => store.get _ _ = _) => apply inde_get; Uniq_not_In
    | |- inde ?L (fun _ _ => u2Z (store.get _ _) = _) => apply inde_u2Z_get; Uniq_not_In
    | |- inde ?L (fun _ _ => u2Z (store.get _ _) + _ = _) => apply inde_u2Z_get_plus; Uniq_not_In
    | |- inde ?L (fun _ _ => s2Z (store.get _ _) = _) => apply inde_s2Z_get; Uniq_not_In
    | |- inde ?L (fun _ _ => _) => done
    | |- inde ?L assert_m.emp => by apply inde_emp
    | _ => trivial
  end.

Require mips_frame.

Ltac inde_remove_duplicates :=
  match goal with
    | |- inde ?L ?P =>
      let L' := seq_ext.remove_duplicates L in
      apply incl_inde with L'
  end.

Ltac Inde_frame :=
  match goal with
    | |- inde (mips_frame.modified_regs _) _ =>
      simpl mips_frame.modified_regs;
      inde_remove_duplicates;
      [Inde | seq_ext.incl_tac ]
  end.

(* NB: Lemma inde_upd_store : forall (P : assert) x z s h,
  inde (x :: nil) P -> P s h -> P (store.upd x z s) h.
*)
Ltac Assert_upd_store :=
  match goal with
    | |- context [store.upd _ _ _] =>
      apply inde_upd_store; [Inde | trivial]
  end.

Ltac Inde_mult :=
  match goal with
    | |- inde_mult (?P ** ?Q) => apply inde_mult_sep_con; Inde_mult
    | |- inde_mult (?P //\\ ?Q) => apply inde_mult_sep_and; Inde_mult
    | |- inde_mult (?E |~> ?E') => apply inde_mult_mapsto
    | |- inde_mult (?V |--> ?L') => apply inde_mult_mapstos
    | |- inde_mult TT => apply inde_mult_TT
    | |- inde_mult (fun _ _ => _ /\ _) => apply inde_mult_and; Inde_mult
    | |- inde_mult (fun _ _ => _) => done
    | _ => trivial (*TODO: try to remove *)
  end.

Ltac Assert_upd_mult :=
  match goal with
    | |- context [store.mthi_op _ _] => apply inde_mult_mthi; Inde_mult
    | |- context [store.mtlo_op _ _] => apply inde_mult_mtlo; Inde_mult
    | |- context [store.multu_op _ _] => apply inde_mult_multu; Inde_mult
    | |- context [store.maddu_op _ _] => apply inde_mult_maddu; Inde_mult
    | |- context [store.msubu_op _ _] => apply inde_mult_msubu; Inde_mult
    | |- context [store.multu_op _ _] => apply inde_mult_multu; Inde_mult
    | |- context [store.mflhxu_op _] => apply inde_mult_mflhxu_op; Inde_mult
  end.

(** Rule out goals of the form:
   <<
   P s h
   =======================
   P (store.upd x ... s) h /
   P (store.multu_op ... s) h /
   P (store.maddu_op ... s) h /
   P (store.msubu_op ... s) h /
   P (store.mthi_op ... s) h /
   P (store.mtlo_op ... s) h /
   P (store.mflhxu_op ... s) h /
   >>
 *)
Ltac Assert_upd :=
  match goal with
    | |- _ =>
      try Assert_upd_mult ;
      try (*(abstract*)Assert_upd_store(*)*)
  end.

Ltac Reg_upd :=
match goal with
| |- context [store.get ?x (store.upd ?x ?z ?s)] =>
  rewrite -> (store.get_upd' x z s); [idtac | by Uniq_neq]
| |- context [store.get ?x (store.upd ?y ?z ?s)] =>
  rewrite -> (store.get_upd x y z s); [idtac | by Uniq_neq]
| |- context [store.get r0 ?s] =>
  rewrite -> (store.get_r0 s)
| id : context [store.get r0 ?s] |- _ =>
  rewrite -> (store.get_r0 s) in id
| |- context [store.get ?x (store.multu_op ?z ?s)] =>
  rewrite -> (store.get_multu_op x z s)
| |- context [store.get ?x (store.maddu_op ?z ?s)] =>
  rewrite -> (store.get_maddu_op x z s)
| |- context [store.get ?x (store.mthi_op ?z ?s)] =>
  rewrite -> (store.get_mthi_op x z s)
| |- context [store.get ?x (store.mtlo_op ?z ?s)] =>
  rewrite -> (store.get_mtlo_op x z s)
| |- context [store.get ?x (store.mflhxu_op ?s)] =>
  rewrite -> (store.get_mflhxu_op x s)
| |- context [store.get ?x (store.msubu_op ?z ?s)] =>
  rewrite -> (store.get_msubu_op x z s)
| |- context [store.utoZ (store.upd ?r ?v ?s)] =>
  rewrite -> store.utoZ_upd
| |- context [store.hi (store.upd ?r ?v ?s)] =>
  rewrite -> store.hi_upd
| |- context [store.lo (store.upd ?r ?v ?s)] =>
  rewrite -> store.lo_upd
| |- context [store.acx (store.upd ?r ?v ?s)] =>
  rewrite -> store.acx_upd
| |- _ => fail
end.

Ltac Decompose_32 lst u lst1 lst2 len1 Hlst :=
  lapply (@list_split (int 32) zero32 (size lst) lst (refl_equal (size lst)) u);
    [let X := fresh in
      (intro X;
	let Y := fresh in
	  (inversion_clear X as [lst1 Y];
	    let Z := len1 in
	      let U := fresh in
		(inversion_clear Y as [Z U];
		  inversion_clear U as [lst2 Hlst]))) | idtac].

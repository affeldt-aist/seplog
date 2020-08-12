(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import List Max ZArith EqNat.
From mathcomp Require Import ssreflect ssrbool eqtype.
Require Import bipl.
Require Import seplog.
Require Import expr_b_dp.
Require Import frag_list_triple.
Require Import frag_list_entail.

Import seplog_Z_m.
Import seplog_Z_m.assert_m.expr_m.
Import seplog_Z_m.assert_m.

Local Open Scope heap_scope.
Local Open Scope seplog_cmd_scope.
Local Open Scope seplog_hoare_scope.

(** swap the value of two cells *)
Local Close Scope Z_scope.

Definition i : var.v := 1.
Definition j : var.v := 2.
Definition x : var.v := 4.
Definition y : var.v := 3.
Definition vx : var.v := 5.
Definition vy : var.v := 6.

Definition swap (x y:var.v) : @while.cmd cmd0 expr_b :=
  i <-* var_e x;
  j <-* var_e y;
  var_e x *<- var_e j;
  var_e y *<- var_e i.

Definition swap_precond (x y:var.v) (vx vy : nat) : assrt :=
  (true_b, star (singl (var_e x) (var_e vx)) (singl (var_e y) (var_e vy))).

Definition swap_postcond (x y:var.v) (vx vy : nat) : assrt :=
  (true_b, star (singl (var_e x) (var_e vy)) (singl (var_e y) (var_e vx))).

(** with bigtoe *)

Lemma swap_verif :
  {{ assrt_interp (swap_precond x y vx vy) }}
  swap x y
  {{ Assrt_interp ((swap_postcond x y vx vy) :: nil) }}.
Proof.
rewrite /swap_precond /swap_postcond.
eapply tritra_use.
by simpl; intuition.
rewrite /x /y /i /j /vx /vy.
by Tritra.
Qed.

(*
intros.
unfold swap_precond.
unfold swap_postcond.
eapply tritra_use.
simpl; intuition.
unfold x; unfold y; unfold i; unfold j; unfold vx; unfold vy.
Tritra.
*)

Local Open Scope seplog_assert_scope.

Lemma tmp : forall (P Q:assert), P ===> Q ->
  P ===> (fun s h => Q s h \/ False).
Proof.
rewrite /while.entails; intros.
auto.
Qed.

Lemma swap_verif_step_by_step :
  {{ assrt_interp (swap_precond x y vx vy) }}
  swap x y
  {{ Assrt_interp ((swap_postcond x y vx vy) :: nil) }}.
Proof.
rewrite /swap_precond /swap_postcond.
eapply tritra_use.
by simpl; intuition.
rewrite /x /y /i /j /vx /vy.

Rotate_tritra_sig_lhs.
apply tritra_lookup.
by intros; omegab.

Rotate_tritra_sig_lhs.
eapply tritra_subst_lookup2.
by intros; omegab.
by simpl; intuition.

apply tritra_subst_mutation.
simpl.
Rotate_tritra_sig_lhs.
apply tritra_mutation.
by do 2 intro; omegab.

apply tritra_subst_mutation.
simpl.
Rotate_tritra_sig_lhs.
eapply tritra_mutation.
by do 2 intro; omegab.

apply tritra_subst_elt.
simpl.
apply tritra_entail.
rewrite /Assrt_interp.
apply tmp.
apply entail_soundness.
by Entail.
Qed.

(*intros.
unfold swap_precond.
unfold swap_postcond.
eapply tritra_use.
simpl; intuition.
unfold x; unfold y; unfold i; unfold j; unfold vx; unfold vy.
Rotate_tritra_sig_lhs.
eapply tritra_lookup.
intros; omegab.
Rotate_tritra_sig_lhs.
eapply tritra_subst_lookup2.
intros; omegab.
simpl; intuition.
Rotate_tritra_sig_lhs.
eapply tritra_subst_mutation.
simpl.
eapply tritra_mutation.
intros; omegab.
eapply tritra_subst_mutation.
simpl.
Rotate_tritra_sig_lhs.
eapply tritra_mutation.
intros; omegab.
eapply tritra_subst_elt.
simpl.
eapply tritra_entail.
eapply Decompose_Assrt_interp; left.
eapply entail_soundness; Entail.
*)

Require Import frag_list_vcg.

Lemma swap_verif' :
  {{ Assrt_interp ((swap_precond x y vx vy) :: nil) }}
  swap x y
  {{ Assrt_interp ((swap_postcond x y vx vy) :: nil) }}.
Proof.
rewrite /swap_precond /swap_postcond /swap /x /y /i /j /vx /vy.

Local Open Scope frag_list_vc_scope.

match goal with
|- {{ _ }} ?C {{ _ }} =>
  replace C with (frag_list_vcg.proj_cmd
    (1 <-* var_e 4 ;
    (2 <-* var_e 3 ;
    (var_e 4 *<- var_e 2 ;
    (var_e 3 *<- var_e 1)))))
end.

Local Close Scope frag_list_vc_scope.

apply bigtoe_fun_correct.
compute; reflexivity.
reflexivity.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int multi_int.
Import MachineInt.
Require Import mips_bipl mapstos.
Import mips_bipl.expr_m.
Import mips_bipl.assert_m.

Local Open Scope machine_int_scope.
Local Open Scope heap_scope.
Local Open Scope mips_assert_scope.

(** construct a heap from a list of int 32's *)

Definition list2heap (a : nat) (l : list (int 32)) : heap.t :=
  map_prop_m.mk_finmap (zip (iota a (size l)) l).

Lemma dom_list2heap l x : heap.dom (list2heap x l) = iota x (size l).
Proof.
rewrite /list2heap -heap.elts_dom map_prop_m.elts_mk_finmap; last first.
  rewrite unzip1_zip /= ?size_iota //; by apply ordset.ordered_iota.
by rewrite -/(unzip1 _) unzip1_zip // size_iota.
Qed.

Lemma cdom_list2heap l x : heap.cdom (list2heap x l) = l.
Proof.
rewrite /list2heap -heap.elts_cdom map_prop_m.elts_mk_finmap; last first.
  rewrite unzip1_zip /= ?size_iota //; by apply ordset.ordered_iota.
by rewrite -/(unzip2 _) unzip2_zip // size_iota.
Qed.

Lemma disj_list2heap l n h : disj (iota n (size l)) (heap.dom h) -> list2heap n l # h.
Proof. move=> ?; by rewrite heap.disjE; apply/seq_ext.disP; rewrite dom_list2heap. Qed.

Local Open Scope zarith_ext_scope.
Local Open Scope mips_expr_scope.

Lemma mapstos_list2heap : forall l n e s, u2Z ( [ e ]e_ s ) = 4 * Z_of_nat n ->
  u2Z ( [ e ]e_ s ) + 4 * (Z_of_nat (size l) - 1) < Zbeta 1 ->
  (e |--> l) s (list2heap n l).
Proof.
elim=> [n e s e_mod e_fit | hd tl IH v n0 s Hv Hn /=].
- split; last by [].
  apply Zdivide_mod.
  exists (Z_of_nat n); by rewrite mulZC.
- destruct tl as [|i tl].
  + rewrite /list2heap /= heap.unionhe.
    exists (heap.sing v hd), heap.emp; split; first by apply heap.disjhe.
    split; first by rewrite heap.unionhe.
    split; first by exists v.
    split; last by [].
    apply u2Z_add_mod => //.
    apply Zdivide_mod.
    exists (Z_of_nat v); by rewrite mulZC.
  + rewrite [i :: _]lock /list2heap /= -lock.
    apply assert_m.con_cons.
    * apply heap.disj_sym, disj_list2heap.
      apply/disP; by rewrite heap.dom_sing dis_seq_singl.
    * by exists v.
    * apply (mapstos_ext (int_e ([ n0 ]e_s `+ four32)) s) => //.
      apply IH.
      - rewrite u2Z_add_Z2u //; last first.
          rewrite (_ : Z_of_nat _ - 1 = 1 + Z_of_nat (size tl)) in Hn; last first.
            rewrite [size _]/=; omegaz.
          rewrite -Zbeta1E; lia.
        rewrite Z_S Hv; ring.
      - rewrite u2Z_add_Z2u //; last first.
          rewrite !Z_S in Hn; rewrite -Zbeta1E; lia.
        rewrite (_ : Z_of_nat _ - 1 = Z_of_nat (size (i :: tl))) in Hn; last by rewrite [size _]/=; omegaz.
        lia.
Qed.

Lemma mapstos_inv_list2heap : forall l e s h, (e |--> l) s h ->
  u2Z ( [ e ]e_ s) + 4 * Z_of_nat (size l) < Zbeta 1 ->
  h = list2heap '|u2Z ( [ e ]e_ s `>> 2)| l.
Proof.
elim=> [e s h Hmem Hfit /= | hd tl IH e s h].
- rewrite /= in Hmem.
  by case: Hmem.
- rewrite [assert_m.mapstos _ _]/=.
  case=> h1 [h2 [Hdisj [Hunion [Hmem1 Hmem2]]]] Hinmem.
  case: Hmem1 => loc [H1 H2].
  rewrite /= in H2 *.
  have -> : '|u2Z ( [ e ]e_ s `>> 2)| = loc.
    rewrite (@shrl_2 _ (Z_of_nat loc)) // Z2uK //.
    by rewrite Zabs_nat_Z_of_nat.
    split; first by apply Zle_0_nat.
    move: (max_u2Z ( [ e ]e_ s)).
    rewrite H1 (_ : 2 ^^ 32 = 2 ^^ 30 * 4) // mulZC => X.
    apply Zmult_gt_0_lt_reg_r in X => //; lia.
  rewrite /list2heap /=.
  have <- : '|u2Z ([ e ]e_ s `+ four32 `>> 2)| = S loc.
    move: (@u2Z_shrl _ ([ e ]e_ s `+ four32) 2 refl_equal) => // X.
    rewrite [_ ^^ _]/= (@u2Z_rem'' _ _ _ (1 + Z_of_nat loc)) in X; last first.
      rewrite u2Z_add_Z2u // H1.
      + rewrite [_ ^^ _]/=; ring.
      + rewrite Z_S in Hinmem; rewrite -Zbeta1E; lia.
    rewrite addZ0 u2Z_add_Z2u // in X; last first.
      rewrite Z_S in Hinmem; rewrite -Zbeta1E; lia.
    have -> : u2Z (eval e s `+ four32 `>> 2) = 1 + Z_of_nat loc by lia.
    rewrite Zabs_nat_Zplus //; last exact/Zle_0_nat.
    by rewrite Zabs_nat_Z_of_nat.
  move: {IH}(IH _ _ _ Hmem2).
  rewrite /list2heap.
  move=> <- //; last first.
    rewrite [eval _ _]/= u2Z_add_Z2u //.
    + rewrite [size _]/= Z_S in Hinmem; lia.
    + rewrite Z_S in Hinmem; rewrite -Zbeta1E; lia.
  by rewrite -H2.
Qed.

Lemma inv_list2heap P l e s h : (P ** e |--> l) s h ->
  u2Z ([e ]e_ s) + 4 * Z_of_nat (size l) < Zbeta 1 ->
  @seq_ext.inc heap.l
  (iota '|u2Z ([ e ]e_ s) / 4| (size l))
  (heap.dom h).
Proof.
move=> Hmem Hfit.
case: Hmem => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
apply mapstos_inv_list2heap in Hh2 => //.
rewrite h1Uh2.
set d := iota _ _.
rewrite (_ : d = heap.dom h2).
  apply/seq_ext.incP => i Hi.
  apply/seq_ext.inP.
  rewrite heap.unionC //.
  apply heap.in_dom_union_L.
  by apply/seq_ext.inP.
by rewrite /d Hh2 dom_list2heap u2Z_shrl'.
Qed.

Lemma mapstos_inv_proj_list2heap P l e s h : (P ** e |--> l) s h ->
  u2Z ( [ e ]e_ s) + 4 * Z_of_nat (size l) < Zbeta 1 ->
  heap.proj h (iota '|(u2Z ([ e ]e_ s) / 4)| (size l)) =
  list2heap '|u2Z ( [ e ]e_ s `>> 2)| l.
Proof.
move=> HP Hfit.
case: HP => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
apply mapstos_inv_list2heap in Hh2 => //.
rewrite h1Uh2.
set d2 := iota _ _.
have -> : d2 = heap.dom h2 by rewrite /d2 Hh2 dom_list2heap u2Z_shrl'.
rewrite heap.proj_union_R_dom; last exact/heap.disj_sym.
by rewrite heap.proj_itself.
Qed.

Local Close Scope zarith_ext_scope.

(** extract a list of contiguous int 32's from a heap *)

Definition heap2list (b : heap.l) (n : nat) (h : heap.t) : list heap.v :=
  heap.cdom (heap.proj h (seq.iota b n)).

Lemma len_heap2list : forall (n : nat) (a : heap.l) h,
  List.incl (iota a n : list heap.l) (heap.dom h) -> size (heap2list a n h) = n.
Proof.
move=> n a h H.
have {}H : seq_ext.inc (seq.iota a n : seq.seq ssrnat.nat_eqType) (heap.dom h).
  by apply/seq_ext.incP.
apply heap.dom_proj_exact in H; last first.
  by apply ordset.ordered_iota.
by rewrite /heap2list heap.size_cdom_dom H seq.size_iota.
Qed.

Lemma heap2list2heap : forall n z l, size l = n -> heap2list z n (list2heap z l) = l.
Proof.
elim => [z [] //= _ | n IH z [|h t] // [len_t] ].
- by rewrite /heap2list heap.proj_emp heap.cdom_emp.
- rewrite /heap2list /list2heap /= heap.proj_union_sing; last first.
    by rewrite seq.in_cons eqxx.
  rewrite heap.cdom_union_sing /=.
  + congr cons.
    rewrite heap.dom_proj_cons.
    * exact: IH.
    * by rewrite dom_list2heap // mem_iota ltnn.
  + apply order.lt_lb => m.
    case/heap.in_dom_proj_inter => Hm1 Hm2.
    rewrite dom_list2heap // in Hm1.
    rewrite /heap.ltl /order.NatOrder.ltA /ltn /=.
    move: Hm1.
    by rewrite mem_iota => /andP[].
Qed.

(* TODO: generalize? *)
Lemma heap2list_list2heap_union n z l h : size l = n ->
  list2heap z l # h ->
  heap2list z n (list2heap z l \U h) = heap2list z n (list2heap z l).
Proof.
move=> Hn Hdisj.
rewrite /heap2list.
move: (dom_list2heap l z).
rewrite Hn => <-.
by rewrite heap.proj_union_L_dom // heap.proj_itself.
Qed.

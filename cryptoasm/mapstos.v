(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import mips_bipl.

Local Open Scope Z_scope.
Local Open Scope heap_scope.
Import expr_m.
Import assert_m.
Local Open Scope zarith_ext_scope.
Local Open Scope mips_assert_scope.

Local Open Scope mips_expr_scope.

Lemma mapstos_decompose_generic n lst nj : forall lst1 (w : int 32) lst2 e s h ,
  size lst = n ->
  size lst1 = nj ->
  lst = lst1 ++ (w :: nil) ++ lst2 ->
  (e |--> lst) s h ->
  (e |--> lst1 **
    (e \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) |~> int_e w) **
    (e \+ int_e (Z2u 32 (Z_of_nat (4 * nj + 4))) |--> lst2)) s h.
Proof.
move: nj n lst.
elim.
- move=> n lst [] // w lst2 e s h Hlst _ Hwlst2 Hsmh.
  rewrite Hwlst2 /= in Hsmh.
  exists heap.emp; exists h.
  split; first by apply heap.disjeh.
  split; first by rewrite heap.unioneh.
  split.
    split; last by done.
    case: Hsmh => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
    case: Hh1 => x [] -> _.
    by rewrite mulZC Z_mod_mult.
  move: Hsmh; apply monotony => h' // Hh'.
  move: Hh'; apply mapsto_ext => //=.
  by rewrite addi0.
- move=> n IH n' lst [|hd1 tl1] // w lst2 e s h Hlst; case=> Hlst1 Hlst1wlst2 Hsmh.
  rewrite Hlst1wlst2 /= in Hsmh.
  rewrite [e |--> _]/=.
  rewrite !assert_m.conAE.
  move: Hsmh; apply monotony => // h1 Hh1.
  destruct lst as [|lsta lstb] => //.
  destruct n' as [|n'] => //.
  have : size (tl1 ++ (w :: nil) ++ lst2)%SEQ = n'.
    case: Hlst => Hlst.
    rewrite -Hlst /=.
    simpl in Hlst1wlst2.
    by case: Hlst1wlst2 => ? <-.
  move/(IH n' (tl1 ++ (w :: nil) ++ lst2) tl1 w lst2 (e \+ int_e four32) s h1) => {IH}.
  move/(_ Hlst1 (refl_equal _) Hh1).
  apply monotony => // h2.
  apply monotony => // h3.
  + apply mapsto_ext => //.
      set x := Z_of_nat _. set y := Z_of_nat _.
      rewrite /= addA /four32 add_Z2u //; last by apply Zle_0_nat.
      repeat f_equal.
      rewrite /x /y !inj_mult.
      by omegaz.
  + apply mapstos_ext => //.
    set x := Z_of_nat _. set y := Z_of_nat _.
    rewrite /= addA /four32 add_Z2u //; last by apply Zle_0_nat.
    repeat f_equal.
    rewrite /x /y inj_plus inj_mult inj_plus inj_mult.
    by omegaz.
Qed.

Lemma mapstos_compose_generic n lst nj : forall lst1 (w : int 32) lst2 e e' e'' s h,
  size lst = n ->
  size lst1 = nj ->
  lst = lst1 ++ (w :: nil) ++ lst2 ->
  [ e' ]e_ s = [ e \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) ]e_ s ->
  [ e'' ]e_ s = [ e \+ int_e (Z2u 32 (Z_of_nat (4 * nj + 4))) ]e_ s ->
  (e |--> lst1 **
    (e' |~> int_e w) **
    (e'' |--> lst2)) s h ->
  (e |--> lst) s h.
Proof.
move: nj n lst.
elim => //.
- move=> n lst [| _ _] // w lst2 e e' e'' s h Hlenlst _ Hlst He' He'' HP.
  rewrite /= in Hlst.
  rewrite Hlst /=.
  set P := _ ** _.
  rewrite -(con_emp_equiv P) conCE /P {P}.
  move: HP; apply monotony => h'.
    by case.
  apply monotony => h1.
    apply mapsto_ext => //.
    by rewrite He' muln0 /= addi0.
  apply mapstos_ext.
  by rewrite He'' muln0 add0n.
- move=> n IH n' lst [_|hd1 tl1] // w lst2 e e' e'' s h Hlenlst Hlentl1 Hlst He' He'' HP.
  case: Hlentl1 => Hlentl1.
  rewrite /= in HP *.
  rewrite !assert_m.conAE in HP.
  rewrite Hlst /=.
  move: HP.
  apply monotony => // h1 Hh1.
  destruct lst as [|ht tl] => //.
  destruct n' as [|n'] => //.
  case: Hlenlst => Hlenlst.
  apply (IH n' (tl1 ++ (w :: nil) ++ lst2)) in Hh1 => //.
  + rewrite -Hlenlst.
    rewrite /= in Hlst.
    by case : Hlst => ? ->.
  + rewrite He' [muln]lock /= -lock addA /four32 add_Z2u //; last by apply Zle_0_nat.
    repeat f_equal.
    rewrite !inj_mult.
    omegaz.
  + rewrite He'' [muln]lock /= -lock addA /four32 add_Z2u //; last by apply Zle_0_nat.
    repeat f_equal.
    rewrite inj_plus inj_mult inj_plus inj_mult.
    omegaz.
Qed.

Lemma decompose_equiv : forall l1 nj e w l2, size l1 = nj ->
  (e |--> l1 ++ (w :: nil) ++ l2) =
    (e |--> l1 **
      e \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) |~> int_e w **
      e \+ int_e (Z2u 32 (Z_of_nat (4 * nj + 4))) |--> l2).
Proof.
move=> l1 nj e w l2 len_l1.
apply assert_m.assert_ext; split => H.
- eapply mapstos_decompose_generic with (lst := l1 ++ (w :: nil) ++ l2); eauto.
- eapply mapstos_compose_generic with (nj := nj); eauto.
Qed.

(*Lemma mapstos_decompose_generic_P_new : forall n lst nj lst1 (w:int 32) lst2 e s h P,
  length lst = n ->
  length lst1 = nj ->
  lst = lst1 ++ (w::nil) ++ lst2 ->
  (e |--> lst ** P) s h ->
  ((e |--> lst1) **
    (add_e e (int_e (Z2u 32 (Z_of_nat (4 * nj)))) |~> int_e w) **
    (add_e e (int_e (Z2u 32 (Z_of_nat (4 * nj + 4)))) |--> lst2) ** P) s h.
Proof.
  move=> n lst nj lst1 w lst2 e s h P Hlst Hlst1 Hw HP.
  rewrite Hw in HP.
  elim: HP => [h1 [h2 [H5 [H6 [H7 H8] ] ] ] ].
  exists h1; exists h2.
  split => //.
  split => //.
  split => //.
  eapply mapstos_decompose_generic.
  apply Hlst.
  done.
  done.
  rewrite Hw //.
Qed.*)

Lemma mapstos_compose_last : forall lst1 n lst (w : int 32) nj (e e' : expr) s,
  size lst = n -> size lst1 = nj ->
  lst = lst1 ++ w::nil ->
  [ e' ]e_ s = [ e \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) ]e_ s ->
  forall h,
    ((e |--> lst1) ** (e' |~> int_e w)) s h ->
    (e |--> lst) s h.
Proof.
move=> lst1 n lst w nj e e' s Hn Hnj Hlst H2 h H3.
move: (mapstos_compose_generic n lst nj lst1 w nil e e' (e \+ int_e (Z2u 32 (Z_of_nat (4 * nj + 4)))) s h Hn Hnj Hlst H2 (refl_equal ([ e \+ int_e (Z2u 32 (Z_of_nat (4 * nj + 4))) ]e_ s)) ) => X.
apply X => //; clear X.
set P := _ ** _ in H3.
rewrite -(con_emp_equiv P) conCE /P {P} in H3.
rewrite conCE conAE in H3.
have e_4 : u2Z [ e ]e_s mod 4 = 0.
  case: H3 => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
  by apply mapstos_inv_addr in Hh1.
have e'_4 : u2Z [ e' ]e_s mod 4 = 0.
  case: H3 => h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
  rewrite con_emp_equiv in Hh2.
  by apply mapsto_inv_addr in Hh2.
move: H3.
apply monotony => h' //.
apply monotony => h'' //.
rewrite /emp => ?; subst h''.
split; last by done.
rewrite (_ : 0 = 0 mod 4) //.
have X4 : 0 < 4 by done.
apply (proj1 (eqmod_Zmod _ _ _ X4)).
(* TODO: clean *)
apply eqmod_trans with (u2Z ([ e \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) ]e_ s)); last first.
  rewrite -H2.
  apply Zmod_divides in e'_4 => //.
  case: e'_4 => p e'_4.
  rewrite /eqmod.
  exists p.
  lia.
apply eqmod_trans with (u2Z (([ e ]e_ s)) + u2Z (Z2u 32 (Z_of_nat (4 * nj + 4)))).
(* TODO: clean with lemmas *)
- apply eqmod_div with (2 ^^ 30).
  rewrite (_ : 2 ^^ 30 * 4 = 2 ^^ 32) //.
  by apply u2Z_add_eqmod.
- apply eqmod_sym.
  apply eqmod_trans with (u2Z (([ e ]e_ s)) + u2Z (Z2u 32 (Z_of_nat (4 * nj)))).
    + apply eqmod_div with (2 ^^ 30).
      rewrite (_ : 2 ^^ 30 * 4 = 2 ^^ 32) //.
      by apply u2Z_add_eqmod.
    + apply eqmod_sym.
      apply eqmod_trans with (u2Z (([ e ]e_ s)) + u2Z (Z2u 32 (Z_of_nat (4 * nj))) + 4);
        last by exists 1; ring.
      rewrite addZC.
      apply eqmod_sym.
      rewrite -addZA addZC.
      apply eqmod_compat_plus_R.
      rewrite u2Z_Z2u_Zmod; last by apply Zle_0_nat.
      rewrite u2Z_Z2u_Zmod; last by apply Zle_0_nat.
      apply (proj2 (eqmod_Zmod _ _ _ X4)).
      rewrite inj_mult [Z_of_nat 4]/= inj_plus inj_mult [Z_of_nat 4]/=.
      rewrite {2}(_ : 4 = 1 * 4) //.
      rewrite Z_mod_plus // -Zmod_div_mod //; last by apply Zdivide_intro with (2 ^^ 30).
      rewrite -Zmod_div_mod //; last by apply Zdivide_intro with (2 ^^ 30).
      by rewrite {4}(_ : 4 = 1 * 4) // Z_mod_plus.
Qed.

Lemma mapstos_decompose_last_P : forall n lst nj lst1 (w : int 32) e s h P,
  size lst = n ->
  size lst1 = nj ->
  lst = lst1 ++ (w :: nil) ->
  (e |--> lst ** P) s h ->
  ((e |--> lst1) **
    (e \+ int_e (Z2u 32 (Z_of_nat (4 * nj))) |~> int_e w) ** P) s h.
Proof.
move=> n lst nj lst1 w e s h P Hlst Hlst1 Hw HP.
rewrite Hw in HP.
rewrite -conAE.
move: HP; apply monotony => // h1 Hh1.
rewrite -Hw in Hh1.
move: (mapstos_decompose_generic _ _ _ _ _ _ _ _ _ Hlst Hlst1 Hw Hh1) => XX.
move: XX; apply monotony => // h2 Hh2.
set Q := _ |~> _.
rewrite -(con_emp_equiv Q) /Q {Q}.
move: Hh2.
apply monotony => // h3.
by case.
Qed.

Lemma decompose_last_equiv2 : forall n e hd tl, size hd = n ->
  (e |--> hd ++ tl :: nil) =
    (e |--> hd ** e \+ int_e (Z2u 32 (Z_of_nat (4 * n))) |~> int_e tl ).
Proof.
move=> n e hd tl Hlen.
apply assert_m.assert_ext; split=> H.
- apply assert_m.con_emp.
  rewrite conAE.
  eapply mapstos_decompose_last_P; last 2 first.
    reflexivity.
    by apply assert_m.con_emp'.
    reflexivity.
    done.
- by eapply mapstos_compose_last; eauto.
Qed.

Lemma decompose_last_equiv : forall e hd tl,
  (e |--> hd ++ tl :: nil) =
    (e |--> hd ** e \+ int_e (Z2u 32 (Z_of_nat (4 * (size hd)))) |~> int_e tl ).
Proof.
move=> e hd tl.
apply assert_m.assert_ext; split=> H.
- apply assert_m.con_emp.
  rewrite conAE.
  eapply mapstos_decompose_last_P; last 2 first.
    reflexivity.
    by apply assert_m.con_emp'.
    reflexivity.
    done.
- eapply mapstos_compose_last; last by apply H.
  reflexivity.
  reflexivity.
  done.
  done.
Qed.

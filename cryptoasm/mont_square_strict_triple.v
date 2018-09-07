(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext machine_int multi_int uniq_tac.
Import MachineInt.
Require Import mips_seplog mips_frame mips_tactics mips_contrib mapstos.
Require Import mont_mul_strict_prg.
Require Import mont_square_triple multi_lt_triple multi_sub_u_u_L_triple.
Import expr_m.
Import assert_m.

Local Open Scope machine_int_scope.
Local Open Scope eqmod_scope.
Local Open Scope heap_scope.
Local Open Scope uniq_scope.
Local Open Scope mips_expr_scope.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope multi_int_scope.
Local Open Scope zarith_ext_scope.

Section mont_square_strict.

Variables k alpha x z m one ext int_ X_ Y_ M_ Z_ quot C t s_ : reg.

Lemma mont_square_strict_verif :
  uniq(k, alpha, x, z, m, one, ext, int_, X_, Y_, M_, Z_, quot, C, t, s_, r0) ->
  forall nk valpha vx vm vz X M,
  u2Z (M `32_ 0) * u2Z valpha =m -1 {{ \B^1 }} ->
  size X = nk -> size M = nk -> u2Z vz + 4 * Z_of_nat nk.+1 < \B^1 ->
  \S_{ nk } X < \S_{ nk } M ->
  {{ fun s h => [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
    u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
    (var_e x |--> X ** var_e z |--> nseq nk zero32 ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\ store.multi_null s}}
  mont_mul_strict k alpha x x z m one ext int_ X_ Y_ M_ Z_ quot C t s_
  {{ fun s h => exists Z, size Z = nk /\ [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
    u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
    (var_e x |--> X ** var_e z |--> Z ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
    \B^nk * \S_{ nk } Z =m \S_{ nk } X * \S_{ nk } X {{ \S_{ nk } M }} /\ \S_{ nk } Z < \S_{ nk } M}}.
Proof.
move=> Hset nk valpha vx vm vz X M Halpha HlenX HlenM Hnz HXM.
rewrite /mont_mul_strict.

(**  montgomery k alpha x y z m_ one ext int_ X_ Y_ M_ Z_ quot C t s_ ; *)

apply while.hoare_seq with ((fun s h => exists Z, size Z = nk /\
  [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M) s h /\
  \B^nk * \S_{nk.+1} (Z ++ [C]_s :: nil) =m \S_{ nk } X * \S_{ nk } X {{ \S_{ nk } M }} /\
  \S_{nk.+1} (Z ++ [C]_s :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk.-1) **
(var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32
  ** var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32)).

apply (hoare_prop_m.hoare_stren ((fun s h => [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e z |--> nseq nk zero32 ** var_e m |--> M) s h /\ store.multi_null s) **
(var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32
  ** var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32))).

move=> s h [r_x [r_z [r_m_ [r_k [r_alpha [Hmem Hmultiplier]]]]]].

rewrite assert_m.conCE !assert_m.conAE
  decompose_last_equiv size_nseq !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.

rewrite assert_m.conCE !assert_m.conAE.
move: Hmem; apply monotony=> // h' Hmem.
rewrite decompose_last_equiv HlenM in Hmem.
rewrite !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
by move: Hmem; apply monotony => // h'' Hmem.

apply frame_rule_R => //.
- eapply mont_square_triple; eauto.
  apply: (ltZ_trans _ Hnz).
  rewrite Z_S mulZDr !addZA -{1}[_ + _]addZ0; exact/ltZ_add2l.
- by Inde_frame.

apply pull_out_exists_con => Z.

apply (hoare_prop_m.hoare_stren (!(fun s => size Z = nk ) **
  (fun s h => [x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
    u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
    \B^nk * \S_{nk.+1} (Z ++ [C]_s :: nil) =m \S_{ nk } X * \S_{ nk } X {{ \S_{ nk } M }} /\
    \S_{nk.+1} (Z ++ [C]_s :: nil) < 2 * \S_{ nk } M /\ u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk.-1 /\
    ((var_e x |--> X ** var_e z |--> Z ** var_e m |--> M
      ** var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32
        ** var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h)))).

move=> s h [h1 [h2 [Hdisj [Hunion [[len_Z [r_x [r_z [r_m [r_k [r_alpha [Hmem [Sum_Z1 [Sum_Z2 r_t]]]]]]]]] Hmem2]]]]].
exists heap.emp, (h1 \U h2); repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.
rewrite -2!assert_m.conAE; Compose_sepcon h1 h2 => //.
by rewrite conAE.

apply pull_out_bang => len_Z.

(**  ifte_beq C, r0 thendo *)

apply while.hoare_ifte.

(**    (multi_lt_prg k z m_ X_ Y_ int_ ext Z_ M_; *)

apply (hoare_prop_m.hoare_stren (fun s h =>
  (([x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
    u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
    \B^nk * \S_{nk.+1} (Z ++ zero32 :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}}) /\
  \S_{nk.+1} (Z ++ zero32 :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk.-1 /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M **
    var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 **
      var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h))).

move=> s h [ [r_x [r_z [r_m [r_k [r_alpha [Sum_Z1 [Sum_Z2 [r_t Hmem]]]]]]]] HbeqC0].

rewrite /= store.get_r0 in HbeqC0; move/eqP/u2Z_inj in HbeqC0.
by rewrite HbeqC0 in Sum_Z1 Sum_Z2.

apply (hoare_prop_m.hoare_stren ((fun s h => (u2Z [k]_s = Z_of_nat nk /\
  [z]_s = vz /\ [m]_s = vm /\ (var_e z |--> Z ** var_e m |--> M) s h)) **
((fun s h => [x]_s = vx /\ [alpha]_s = valpha /\
  \B^nk * \S_{nk.+1} (Z ++ zero32 :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}} /\
  \S_{nk.+1} (Z ++ zero32 :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk.-1) //\\
(var_e x |--> X ** var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 **
  var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32)))).

move=> s h [[r_x [r_z [r_m [r_k [r_alpha Sum_Z1]]]]] [Sum_Z2 [r_t Hmem]]].

have {Hmem}Hmem : ((var_e z |--> Z ** var_e m |--> M) **
  (var_e x |--> X ** var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 **
    var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32)) s h.
  by assoc_comm Hmem.
case: Hmem => h1 [h2 [Hdisj [Hunion [H1 H2]]]].
by exists h1, h2.

apply while.hoare_seq with ((fun s h => u2Z [k]_s = Z_of_nat nk /\
  [z]_s = vz /\ [m]_s = vm /\
  ((\S_{ nk } Z < \S_{ nk } M /\ [int_]_s = one32 /\ [ext]_s = zero32) \/
    (\S_{ nk } Z > \S_{ nk } M /\ [int_]_s = zero32 /\ [ext]_s = one32) \/
    (\S_{ nk } Z = \S_{ nk } M /\ [int_]_s = zero32 /\ [ext]_s = zero32)) /\
  (var_e z |--> Z ** var_e m |--> M) s h) **
((fun s h => [x]_s = vx /\ [alpha]_s = valpha /\
  (\B^nk * \S_{ nk.+1 } (Z ++ zero32 :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}}) /\
  \S_{ nk.+1 } (Z ++ zero32 :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk.-1) //\\
(var_e x |--> X ** var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 **
  var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32))).

apply frame_rule_R.
- eapply multi_lt_triple; eauto.
  by Uniq_uniq r0.
- by Inde_frame.
- move=> ?; by Inde_mult.

(**    ifte_beq int_, r0 thendo *)

apply while.hoare_ifte.

(**      multisub k one z m_ z ext int_ quot C Z_ X_ Y_ X_
    elsedo
      nop)
  elsedo *)

apply (hoare_prop_m.hoare_stren (!(fun s => \S_{ nk } M <= \S_{ nk } Z) **
  (fun s h => [z]_s = vz /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\
    [x]_s = vx /\ [alpha]_s = valpha /\
    (\B^nk * \S_{ nk.+1 } (Z ++ zero32 :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}}) /\
    \S_{ nk.+1 } (Z ++ zero32 :: nil) < 2 * \S_{ nk } M /\
    u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk.-1 /\
    ((var_e z |--> Z ** var_e m |--> M) **
      (var_e x |--> X ** var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 **
        var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32)) s h))).

move=> s h [[h1 [h2 [Hdisj [Hunion [[r_k [r_z [r_m [Hor Hmem]]]] [[r_x [r_alpha [Sum_Z1 [Sum_Z2 r_t]]]] Hmem2]]]]]] Hbeqint0].

rewrite /= store.get_r0 in Hbeqint0; move/eqP in Hbeqint0.

exists heap.emp, (h1 \U h2); repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.
case : Hor.
- case => _ [Hor _]; by rewrite Hor /one32 /zero32 2?Z2uK in Hbeqint0.
- case; [case=> H _; exact/ltZW/Z.gt_lt | case=> -> _; exact/leZZ].
- by exists h1, h2.

apply pull_out_bang => HZM.

apply (hoare_prop_m.hoare_stren ((fun s h => ([z]_s = vz /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ (var_e z |--> Z ** var_e m |--> M) s h)) **
(fun s h => [x]_s = vx /\ [alpha]_s = valpha /\
  (\B^nk * \S_{ nk.+1 } (Z ++ zero32 :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}}) /\
  \S_{ nk.+1 } (Z ++ zero32 :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk.-1 /\
  (var_e x |--> X ** var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 **
      var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h))).

move=> s h [r_z [r_m [r_k [r_x [r_alpha [Sum_Z1 [Sum_Z2 [Hgpt Hmem]]]]]]]].

case: Hmem => h1 [h2 [Hdisj [Hunion [H1 H2]]]].
by exists h1, h2.

apply (hoare_prop_m.hoare_weak ((fun s h => exists Z', size Z' = nk /\ [z]_s = vz /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [C]_s = zero32 /\ (var_e z |--> Z' ** var_e m |--> M) s h /\
  \S_{ nk } Z' = \S_{ nk } Z - \S_{ nk } M) **
(fun s h => [x]_s = vx /\ [alpha]_s = valpha /\
  (\B^nk * \S_{ nk.+1 } (Z ++ zero32 :: nil) =m \S_{ nk } X * \S_{ nk } X {{ \S_{ nk } M }}) /\
  \S_{ nk.+1 } (Z ++ zero32 :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk.-1 /\
  (var_e x |--> X ** var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 **
    var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h))).

move=> s h [h1 [h2 [Hdisj [Hunion [[Z' [len_Z' [r_z [r_m [r_k [HC [Hmem1 HSumSub]]]]]]] [r_x [r_alpha [Sum_Z1 [Sum_Z2 [r_t Hmem2]]]]]]]]]].
exists Z'; repeat (split; trivial).

move: (assert_m.con_cons _ _ _ _ _ Hdisj Hmem1 Hmem2).
rewrite -Hunion => Htmp.
rewrite 2!decompose_last_equiv len_Z' HlenM; by assoc_comm Htmp.

rewrite HSumSub.
rewrite (lSum_cut_last _ Z) // in Sum_Z1; last by rewrite size_cat /= len_Z addnC.
rewrite subn1 [_.+1.-1]/= /= /zero32 Z2uK // mulZ0 // addZ0 in Sum_Z1.
rewrite mulZBr; exact/eqmod_minmod.

rewrite (lSum_cut_last _ Z) // in Sum_Z2; last by rewrite size_cat /= len_Z addnC.
rewrite subn1 [_.+1.-1]/= /zero32 Z2uK // mulZ0 // in Sum_Z2.
rewrite HSumSub; omega.

apply frame_rule_R.
- eapply multi_sub_u_u_L_triple_B_le_A; eauto.
  + by Uniq_uniq r0.
  + apply: (ltZ_trans _ Hnz).
    rewrite Z_S mulZDr !addZA -{1}[_ + _]addZ0; exact/ltZ_add2l.
- by Inde_frame.
- move=> ?; by Inde_mult.

apply hoare_nop'.

move=> s h [ [h1 [h2 [Hdisj [Hunion [[r_k [r_z [r_m [Hor Hmem1]]]] [[r_x [r_alpha [Sum_Z1 [Sum_Z2 r_t]]]] Hmem2]]]]]] Hbneint0].
exists Z; repeat (split; trivial).

move: (assert_m.con_cons _ _ _ _ _ Hdisj Hmem1 Hmem2).
rewrite -Hunion => Htmp.
rewrite 2!decompose_last_equiv len_Z HlenM; by assoc_comm Htmp.

rewrite (lSum_cut_last _ Z) // in Sum_Z1; last by rewrite size_cat /= len_Z addnC.
by rewrite subn1 /zero32 Z2uK // mulZ0 addZ0 in Sum_Z1.
case: Hor.
- by case.
- rewrite /= store.get_r0 in Hbneint0; move/eqP in Hbneint0.
  case.
  + case=> _ [Hor _]; by rewrite Hor in Hbneint0.
  + move=> [_ [Hor _]]; by rewrite Hor in Hbneint0.

(** addiu t t four16 *)

apply hoare_addiu with (fun s h => ([x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (\B^nk * \S_{ nk.+1 } (Z ++ [C]_s :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}}) /\
  \S_{ nk.+1 } (Z ++ [C]_s :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk /\ u2Z [C]_s <> u2Z (zero32) /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M **
    var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 **
      var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h)).

move=> s h [[r_x [r_z [r_m [r_k [r_alpha [Sum_Z1 [Sum_Z2 [r_t Hmem]]]]]]]] HbneC0].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
- rewrite sext_Z2u // u2Z_add_Z2u //.
  + rewrite r_t -subn1 inj_minus1 //; last by destruct nk => //; exact/le_n_S/le_O_n.
    ring.
  + rewrite r_t -subn1 inj_minus1; last by destruct nk => //; exact/le_n_S/le_O_n.
    rewrite -Zbeta1E; rewrite Z_S in Hnz; omega.
- rewrite /= store.get_r0 // in HbneC0; by move/eqP : HbneC0.
- by Assert_upd.

(** sw C zero16 t *)

apply hoare_sw_back'' with (fun s h => ([x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  \B^nk * \S_{ nk.+1 } (Z ++ [C]_s :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}} /\
  \S_{ nk.+1 } (Z ++ [C]_s :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk /\ u2Z [C]_s <> u2Z (zero32) /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M **
    var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e [C]_s **
      var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h)).

move=> s h [r_x [r_z [r_m [r_k [r_alpha [Sum_Z1 [Sum_Z2 [r_t [r_C Hmem]]]]]]]]].

have Htmp : [t]_s `+ sext 16 zero16 = [z]_s `+ Z2u 32 (Z_of_nat (4 * nk)).
  rewrite sext_0 addi0; apply u2Z_inj.
  rewrite r_t u2Z_add_Z2u //.
  rewrite r_z inj_mult; ring.
  exact: Zle_0_nat.
  rewrite r_z -Zbeta1E inj_mult [Z_of_nat 4]/=.
  move: (min_u2Z vz) => ?; omegaz.

exists (int_e zero32).
rewrite assert_m.conCE !assert_m.conAE assert_m.conCE !assert_m.conAE assert_m.conCE !assert_m.conAE in Hmem.
move: Hmem; apply monotony => // h'.
exact: mapsto_ext.

apply currying => h0 H0.

repeat (split; trivial).
assoc_comm H0.
exact: mapsto_ext H0.

(*:    addiu ext k one16 ; *)

apply hoare_addiu with (fun s h => ([x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  \B^nk * \S_{ nk.+1 } (Z ++ [C]_s :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}} /\
  \S_{ nk.+1 } (Z ++ [C]_s :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk /\ u2Z [C]_s <> u2Z (zero32) /\
  u2Z [ext]_s = Z_of_nat nk.+1 /\
  (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M **
    var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e [C]_s **
      var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h)).

move=> s h [r_x [r_z [r_m [r_k [r_alpha [Sum_Z1 [Sum_Z2 [r_t [r_C Hmem]]]]]]]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
- rewrite sext_Z2u // u2Z_add_Z2u //.
  + rewrite r_k Z_S; ring.
  + rewrite r_k -Zbeta1E.
    move: (min_u2Z vz) => ?; omegaz.
- by Assert_upd.

(**   multisub ext one z m_ z M_ int_ quot C Z_ X_ Y_ X_). *)

apply (hoare_prop_m.hoare_stren ((fun s h => exists Cint32,
  (\S_{ nk.+1 } (M ++ zero32 :: nil) <= \S_{ nk.+1 } (Z ++ Cint32 :: nil) /\ [C]_s = Cint32) /\ h = heap.emp) **
(fun s h => ([x]_s = vx /\ [z]_s = vz /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (\B^nk * \S_{ nk.+1 } (Z ++ [C]_s :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}}) /\
  \S_{ nk.+1 } (Z ++ [C]_s :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk /\ u2Z [ext]_s = Z_of_nat nk.+1 /\
  ((var_e x |--> X ** var_e z |--> Z ** var_e m |--> M **
    var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e [C]_s **
      var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h))))).

move=> s h [r_x [r_z [r_m [r_k [r_alpha [Sum_Z1 [Sum_Z2 [r_t [r_C [r_ext Hmem]]]]]]]]]].
exists heap.emp, h; repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.
exists ([C]_s); repeat (split; trivial).
rewrite lSum_cut_last; last by rewrite size_cat /= HlenM addnC.
rewrite lSum_cut_last; last by rewrite size_cat /= len_Z addnC.
rewrite /= subn1 /zero32 Z2uK // mulZ0 addZ0.
move: (max_lSum nk M); rewrite -ZbetaE => ?.
move: (min_lSum nk Z) (min_lSum nk M) => ? ?.
have ? : 0 < u2Z [C]_s.
  rewrite /zero32 Z2uK // in r_C.
  apply Zle_neq_lt; by [apply min_u2Z | contradict r_C].
simpl.
apply (@leZ_trans (\S_{ nk } Z + \B^nk * 1)); first by omega.
apply leZ_add2l, leZ_pmul2l; by [omega | ].

apply pull_out_exists_con => Cint32.

apply (hoare_prop_m.hoare_stren (
  !(fun s => \S_{ nk.+1 } (M ++ zero32 :: nil) <= \S_{ nk.+1 } (Z ++ Cint32 :: nil)) **
  (fun s h => [ x ]_s = vx /\ [ z ]_s = vz /\ [ m ]_s = vm /\
    u2Z [ k ]_s = Z_of_nat nk /\ [ alpha ]_s = valpha /\ [ C ]_s = Cint32 /\
    (\B^nk * \S_{ nk.+1 } (Z ++ [ C ]_s :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}}) /\
    \S_{ nk.+1 } (Z ++ [ C ]_s :: nil) < 2 * \S_{ nk } M /\
    u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk /\ u2Z [ext]_s = Z_of_nat nk.+1 /\
    (var_e x |--> X ** var_e z |--> Z ** var_e m |--> M **
      var_e z \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e [ C ]_s **
        var_e m \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h))).

move=> s h [h1 [h2 [Hdisj [Hunion [[[Sum_Z1 r_C] Hh1] [r_x [r_z [r_m [r_k [r_alpha [Sum_Z2 [Sum_Z3 [r_t [r_ext Hmem]]]]]]]]]]]]]].
by exists h1, h2.

apply pull_out_bang => HZM.

apply (hoare_prop_m.hoare_stren ((fun s h => [z]_s = vz /\
  [m]_s = vm /\ u2Z [ext]_s = Z_of_nat nk.+1 /\
  (var_e z |--> (Z ++ Cint32 :: nil) ** var_e m |--> M ++ zero32 :: nil) s h) **
(fun s h => [x]_s = vx /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (\B^nk * \S_{ nk.+1 } (Z ++ Cint32 :: nil) =m \S_{ nk } X * \S_{ nk } X {{\S_{ nk } M}}) /\
  \S_{ nk.+1 } (Z ++ Cint32 :: nil) < 2 * \S_{ nk } M /\
  u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk /\ (var_e x |--> X) s h))).

move=> s h [r_x [r_z [r_m [r_k [r_alpha [r_C [Sum_Z1 [Sum_Z2 [r_t [r_ext Hmem]]]]]]]]]].

have {Hmem}Hmem : ((var_e z |--> Z ++ Cint32 :: nil ** var_e m |--> M ++ zero32 :: nil) ** (var_e x |--> X)) s h.
  rewrite 2!decompose_last_equiv len_Z HlenM.
  assoc_comm Hmem.
  by rewrite -r_C.
case: Hmem => h1 [h2 [Hdisj [Hunion [H1 H2]]]].
exists h1, h2; repeat (split; trivial).
by rewrite -r_C.
by rewrite -r_C.

apply (hoare_prop_m.hoare_weak ((fun s h => exists Z', size Z' = nk.+1 /\ [z]_s = vz /\
  [m]_s = vm /\ u2Z [ext]_s = Z_of_nat nk.+1 /\ [C]_s = zero32 /\
  (var_e z |--> Z' ** var_e m |--> M ++ zero32 :: nil) s h /\
  \S_{ nk.+1 } Z' = \S_{ nk.+1 } (Z ++ Cint32 :: nil) - \S_{ nk.+1 } (M ++ zero32 :: nil)) **
(fun s h => [x]_s = vx /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
    (\B^nk * \S_{ nk.+1 } (Z ++ Cint32 :: nil) =m \S_{ nk } X * \S_{ nk } X {{ \S_{ nk } M }}) /\
    \S_{ nk.+1 } (Z ++ Cint32 :: nil) < 2 * \S_{ nk } M /\
    u2Z [t]_s = u2Z vz + 4 * Z_of_nat nk /\ (var_e x |--> X) s h))).

move=> s h [h1 [h2 [Hdisj [Hunion [[Z' [len_Z' [r_z [r_m_ [r_ext [HC [Hmem1 Sum_Z']]]]]]] [r_x [r_k [r_alpha [HsumZC2 [HsumZC3 [r_t Hmem2]]]]]]]]]]].

have [Z'' [HlenZ'' HZ'Z'']] :
  exists Z'', size Z'' = nk /\ Z' = Z'' ++ zero32 :: nil.
  have Htmp :  \S_{ nk.+1 } Z' < \S_{ nk.+1 } (M ++ zero32 :: nil).
    rewrite Sum_Z' (lSum_cut_last nk.+1 M); last by rewrite size_cat /= HlenM addnC.
    rewrite !subn1 /zero32 Z2uK // mulZ0 addZ0.
    rewrite (lSum_cut_last nk.+1 M) in HZM; last by rewrite size_cat /= HlenM addnC.
    rewrite subn1 /zero32 Z2uK // mulZ0 addZ0 in HZM.
    rewrite /=.
    apply (@ltZ_leZ_trans (2 * \S_{ nk } M - \S_{ nk } M)); [exact/ltZ_sub2r | omega].
  have Htmp' : \S_{ nk.+1 } Z' < \B^nk.
    rewrite (lSum_cut_last _ M) // in Htmp; last by rewrite size_cat /= HlenM addnC.
    rewrite subn1 [_.+1.-1]/= /zero32 Z2uK // mulZ0 addZ0 in Htmp.
    move: (max_lSum nk M); rewrite -ZbetaE => ?; omega.
  rewrite (lSum_beyond_inv 32 nk.+1 _ nk len_Z').
  exists (take nk Z'); split => //.
  by rewrite size_takel // len_Z'.
  by rewrite subSn // subnn.
  by [].
  by rewrite -ZbetaE.

exists Z''; repeat (split; trivial).

rewrite -HZ'Z'' assert_m.conCE.

exists h1, h2; repeat (split => //).

rewrite HZ'Z'' (lSum_cut_last _ Z'') // in Sum_Z'; last by rewrite size_cat /= HlenZ'' addnC.
rewrite subn1 [_.+1.-1]/= (lSum_cut_last _ M) // in Sum_Z'; last by rewrite size_cat /= HlenM addnC.
rewrite subn1 [_.+1.-1]/= /zero32 Z2uK // mulZ0 2!addZ0 in Sum_Z'.
rewrite Sum_Z' mulZBr; exact: eqmod_minmod.

rewrite HZ'Z'' (lSum_cut_last _ Z'') // in Sum_Z'; last by rewrite size_cat /= HlenZ'' addnC.
rewrite subn1 [_.+1.-1]/= (lSum_cut_last _ M) // in Sum_Z'; last by rewrite size_cat /= HlenM addnC.
rewrite subn1 [_.+1.-1]/= /zero32 Z2uK // mulZ0 2!addZ0 in Sum_Z'.
rewrite Sum_Z'.
apply (@ltZ_leZ_trans (2 * \S_{ nk } M - \S_{ nk } M)); [exact: ltZ_sub2r | omega].

apply frame_rule_R.
- eapply multi_sub_u_u_L_triple_B_le_A; eauto.
  by Uniq_uniq r0.
  by rewrite size_cat /= len_Z addnC.
  by rewrite size_cat /= HlenM addnC.
- by Inde_frame.
- move=> ?; by Inde_mult.
Qed.

End mont_square_strict.

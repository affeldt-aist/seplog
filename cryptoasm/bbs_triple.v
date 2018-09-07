(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext ssrnat_ext seq_ext uniq_tac machine_int.
Require Import multi_int.
Import MachineInt.
Require Import mips_seplog mips_frame mips_contrib mips_tactics mapstos.
Require Import mont_mul_strict_prg bbs_prg.
Require Import mont_mul_strict_init_triple mont_square_strict_init_triple.

Local Open Scope machine_int_scope.
Local Open Scope eqmod_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope heap_scope.
Import expr_m.
Local Open Scope mips_expr_scope.
Import assert_m.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.
Local Open Scope multi_int_scope.

Require Import listbit.

Notation "m ^ n" := (expn m n) : nat_scope. (* TODO: kludge *)

(* TODO: move *)
Lemma take_bits n (a : int n) m : (m < n)%nat ->
  take m (bits ((a `& Z2u n 1) `<< m)) = bits.zeros m.
Proof.
move=> Hmn.
case: (Zeven_odd_dec (u2Z a)) => Ha.
- rewrite int_even_and_1 // shl_zero bits_zeros bits.heads_zeros //; ssromega.
- by rewrite int_odd_and_1 // bits_shl_1 // take_size_cat // size_nseq.
Qed.

(* TODO: move *)
Lemma nth_bits n (a : int n) k : (k < n)%nat ->
  nth true (bits ((a `& Z2u n 1) `<< k)) k = Zodd_bool (u2Z a).
Proof.
move=> H.
case: (Zeven_odd_dec (u2Z a)) => [a_even|a_odd].
- rewrite int_even_and_1 // shl_zero bits_zeros /bits.zeros nth_nseq H.
  rewrite /Zodd_bool.
  by move/ZevenP : a_even => ->.
- rewrite int_odd_and_1 // bits_shl_1 // nth_cat /bits.zeros size_nseq ltnn subnn /=.
  exact/esym/ZoddP.
Qed.

(* TODO: move *)
Lemma drop_bits n (a : int n) k : (k < n)%nat ->
  drop k.+1 (bits ((a `& Z2u n 1) `<< k)) = bits.zeros (n - k.+1).
Proof.
move=> H.
case: (Zeven_odd_dec (u2Z a)) => [a_even|a_odd].
- by rewrite int_even_and_1 // shl_zero bits_zeros /bits.zeros drop_nseq.
- rewrite int_odd_and_1 // bits_shl_1 // -cat1s catA drop_size_cat /=; last first.
    by rewrite /bits.zeros size_cat size_nseq addn1.
  by rewrite -subnDA addn1.
Qed.

Local Open Scope uniq_scope.

Lemma bbs_triple (i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C t s_ b2k B2K_ w' w : reg) :
    uniq(i, L_, l, n, j, thirtytwo, k, alpha, x, y, m, one, ext, int_, X_, Y_,
          M_, quot, C, t, s_, b2k, B2K_, w', w, r0) ->
  forall nk valpha M, u2Z (M `32_ 0) * u2Z valpha =m -1 {{ \B^1 }} ->
  forall nn L, size L = nn ->
  forall X0 Y B2K, size X0 = nk -> size B2K = nk -> size M = nk -> size Y = nk ->
  forall vx vy vm vb2k vl,
  u2Z vy + 4 * Z_of_nat nk.+1 < \B^1 -> u2Z vx + 4 * Z_of_nat nk.+1 < \B^1 ->
  u2Z vl + 4 * Z_of_nat nn < \B^1 -> \S_{ nk } X0 < \S_{ nk } M -> \S_{ nk } B2K < \S_{ nk } M ->
  \S_{ nk } B2K =m \B^nk ^^ 2 {{ \S_{ nk } M }} -> Zodd (\S_{ nk } M) ->
{{ fun s h => u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\
  [y]_s = vy /\ [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\
  [l]_s = vl /\ u2Z [thirtytwo]_s = Z_of_nat 32 /\
  (var_e x |--> X0 ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h }}
bbs i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C t s_ b2k B2K_ w' w
{{ fun s h => exists L X Y, size L = nn /\ size X = nk /\ size Y = nk /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\
  [y]_s = vy /\ [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\
  [l]_s = vl /\ u2Z [thirtytwo]_s = Z_of_nat 32 /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits _) L) = bbs_fun_rec (nn * 32) (\S_{ nk } X0 ^^ 2 mod (\S_{ nk } M)) (\S_{ nk } M) }}.
Proof.
move=> Hset nk valpha M Halpha nn L HlenL X0 Y B2K HlenX0 HlenB2K HlenM HlenY vx
  vy vm vb2k vl Hny Hnx Hnl HSumX0
  HSumB2K HSumB2K1 HoddM.
rewrite /bbs.

(**  addiu i r0 zero16 ;*)

NextAddiu.
move=> s h [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [Hr32 Hmem]]]]]]]]].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(**  addiu L_ l zero16 ;*)

NextAddiu.
move=> s h [[Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [Hr32 Hmem]]]]]]]]] Hri].
rewrite /wp_addiu; repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(**  while (bne i n) ( *)

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists ni L X Y,
 u2Z [i]_s = Z_of_nat ni /\ size L = nn /\ size X = nk /\ size Y = nk /\
 u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\
 [y]_s = vy /\ [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\
 [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
 u2Z [thirtytwo]_s = Z_of_nat 32 /\ (ni <= nn)%nat /\
 (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
 flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
 \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M).

move=> s h [[[Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [Hr32 Hmem]]]]]]]]] Hri] HrL_].
exists O, L, X0, Y; repeat (split; trivial).
by rewrite Hri store.get_r0 sext_Z2u // addi0 Z2uK.
rewrite HrL_ sext_Z2u // addi0 Hrl; ring.
by rewrite mul0n /= take0.
rewrite mul0n /= mulZ1; exact: eqmod_refl.

move=> {L HlenL Y HlenY} s h [[ni [L [X [Y [Hri [HlenL [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hninn [Hmem [Hbbs [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]] Heqni].
rewrite /= in Heqni; move/negPn/eqP/u2Z_inj in  Heqni.
exists L, X, Y; repeat (split; trivial).
have : ni = nn by rewrite Heqni Hrn in Hri; apply Z_of_nat_inj in Hri.
move=> ?; subst ni.
rewrite take_oversize // in Hbbs; by rewrite HlenL.

(**    addiu j r0 zero16 ; *)

clear L HlenL Y HlenY.

NextAddiu.

move=> s h [[ni [L [X [Y [Hri [HlenL [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hninn [Hmem [Hbbs [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]] Hneqin].
rewrite /= in Hneqin.
rewrite /wp_addiu.
repeat Reg_upd; repeat (split; trivial).
exists ni, L, X, Y; repeat (split; trivial).
by Assert_upd.
by rewrite /=; repeat Reg_upd; trivial.

(**    addiu w r0 zero16 ;*)

NextAddiu.

move=> s h [[[ni [L [X [Y [Hri [HlenL [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hninn [Hmem [Hbbs [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]] Hneqin] Hrw].
rewrite /= in Hneqin.
rewrite /wp_addiu.
repeat Reg_upd; repeat (split; trivial).
exists ni, L, X, Y; repeat (split; trivial).
by Assert_upd.
by rewrite /=; repeat Reg_upd.

(**    while (bne j thirtytwo) ( *)

apply (hoare_prop_m.hoare_stren (fun s h => exists ni L, size L = nn /\
 exists X Y, u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ size Y = nk /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\
  [y]_s = vy /\ [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\
  [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ (ni < nn)%nat /\ u2Z [j]_s = 0 /\
  [w]_s = zero32 /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod (\S_{ nk } M)) (\S_{ nk } M) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M)).

move=> s h [[[[ni [L [X [Y [Hregi [HlenL [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hninn [Hmem [Hbbs [Sum_X Sum_M]]]]]]]]]]]]]]]]]]]]]] Hneqni] Hrj] Hrw].
rewrite /= in Hneqni; move/eqP in Hneqni.

exists ni, L; repeat (split; trivial).
exists X, Y; repeat (split; trivial).
rewrite Hregi Hrn in Hneqni.
apply Z_of_nat_inj_neq in Hneqni.
rewrite ltn_neqAle Hninn andbT; exact/eqP.
by rewrite Hrj store.get_r0 add0i (@u2Z_sext 16) Z2uK.
move: Hrw; rewrite sext_Z2u // addi0 store.get_r0; by move/u2Z_inj.

apply pull_out_exists => ni; apply pull_out_exists => L.

apply (hoare_prop_m.hoare_stren (!(fun s => size L = nn) **
 (fun s h => exists X, exists Y, u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ size Y = nk /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\
  [x]_s = vx /\ [y]_s = vy /\ [m]_s = vm /\ [b2k]_s = vb2k /\
  [alpha]_s = valpha /\ [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ (ni < nn)%nat /\ u2Z [j]_s = 0 /\ [w]_s = zero32 /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod (\S_{ nk } M)) (\S_{ nk } M) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M))).

move=> s h [HlenL [X [Y [Hri [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hninn [Hregj [Hrw [Hmem [Hbs [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]].

exists heap.emp, h; repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.
by exists X, Y.

apply pull_out_bang => HlenL.

apply while.hoare_seq with (fun s h => exists X Y vw,
  u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ size Y = nk /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\
  [y]_s = vy /\ [m]_s = vm /\ [b2k]_s = vb2k /\
  [alpha]_s = valpha /\ [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat 32 /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod (\S_{ nk } M)) (\S_{ nk } M) /\
  (ni < nn)%nat /\ [w]_s = vw /\
  bits vw = bbs_fun_rec 32 ((\S_{ nk } X0 ^^ 2 mod (\S_{ nk } M)) ^^ 2 ^ (ni * 32) mod (\S_{ nk } M)) (\S_{ nk } M) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni.+1 * 32) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M).

apply hoare_prop_m.hoare_while_invariant with (fun s h => exists X Y vw nj,
  u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ size Y = nk /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\ [y]_s = vy /\
  [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\ [l]_s = vl /\
  u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\ u2Z [thirtytwo]_s = Z_of_nat 32 /\
  u2Z [j]_s = Z_of_nat nj /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod (\S_{ nk } M)) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj <= 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod (\S_{ nk } M)) ^^ 2 ^ (ni * 32) mod (\S_{ nk } M)) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M).

move=> s h [X [Y [Hri [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hninn [Hrj [Hrw [Hmem [Hbbs [Sum_X X_M]]]]]]]]]]]]]]]]]]]]].

exists X, Y, zero32; exists O; repeat (split; trivial).
by rewrite take0.
rewrite drop0 subn0 /=; exact: bits_zeros.
by rewrite addn0.

move=> s h [[X [Y [vw [nj [Hri [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs [Hninn [Hnj32 [Hrw [Hbbs' [Hbbs'' [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]]]]]] Heqj32].
rewrite /= Hr32 Hrj in Heqj32; move/negPn/eqP/Z_of_nat_inj in Heqj32.
exists X, Y, vw.
subst nj.
rewrite mulSn.
repeat (split; trivial).
rewrite take_oversize // in Hbbs'; by rewrite size_bits.
by rewrite addnC.

(**      mont_mul_strict_init k alpha x x y m one ext int_ X_ B2K_ Y_ M_ quot C t s_; *)

apply (hoare_prop_m.hoare_stren (fun s h => exists vw nj X Y,
  u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ size Y = nk /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\ [y]_s = vy /\
  [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\ [l]_s = vl /\
  u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M)).

move=> s h [ [X [Y [vw [nj [Hri [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs [Hninn [Hnj32 [Hrw [Hbbs' [Hbbs'' [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]]]]]] Hnej32].
rewrite /= Hrj Hr32 in Hnej32. move/eqP/Z_of_nat_inj_neq in Hnej32.
exists vw, nj, X, Y; repeat (split; trivial).
rewrite ltn_neqAle Hnj32 andbT; exact/eqP.

apply pull_out_exists => vw; apply pull_out_exists => nj; apply pull_out_exists => X.

apply (hoare_prop_m.hoare_stren (!(fun s => size X = nk) **
 (fun s h => exists Y, u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ size Y = nk /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\
  [y]_s = vy /\ [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\
  [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M))).

move=> s h [Y [Hri [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs [Hninn [Hnj32 [Hrw [Hbbs' [Hbbs'' [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]]].

exists heap.emp, h; repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.
by exists Y.

apply pull_out_bang => HlenX.

apply while.hoare_seq with (fun s h => exists Y, u2Z [i]_s = Z_of_nat ni /\
 size X = nk /\ size Y = nk /\ u2Z [k]_s = Z_of_nat nk /\
 u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\ [y]_s = vy /\
 [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\
 [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
 u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
 (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
 flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
 (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
 take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
 drop nj (bits vw) = bits.zeros (32 - nj) /\
 \B^nk * \S_{ nk } Y =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj.+1) {{ \S_{ nk } M }} /\ \S_{ nk } Y < \S_{ nk } M).

apply (hoare_prop_m.hoare_stren (!(fun s => \S_{ nk } X < \S_{ nk } M) **
((fun s h => exists Y, size Y = nk /\ [x]_s = vx /\ [y]_s = vy /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e y |--> Y ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h) **
(fun s h => u2Z [i]_s = Z_of_nat ni /\ u2Z [n]_s = Z_of_nat nn /\
  [b2k]_s = vb2k /\ [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
  (var_e x \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 ** var_e l |--> L ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj) {{ \S_{ nk } M }})))).

move=> {HlenX} s h [Y [Hregi [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs [Hninn [Hnj32 [Hrw [Hbbs' [Hbbs'' [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]]].

exists heap.emp, h; repeat split.
by map_tac_m.Disj.
by map_tac_m.Equal.
exact X_M.

have {Hmem}Hmem : ((var_e x |--> X ** var_e y |--> Y ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) **
    (var_e x \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 ** var_e l |--> L ** var_e b2k |--> B2K)) s h.
  rewrite (decompose_last_equiv _ X) HlenX in Hmem.
  by assoc_comm Hmem.
case: Hmem => h1 [h2 [Hdisj [Hunion [Hmem1 Hmem2]]]].
exists h1, h2; repeat (split; trivial).
by exists Y.

apply pull_out_bang => X_M.

apply hoare_prop_m.hoare_weak with ((fun s h => exists Y, size Y = nk /\ [x]_s = vx /\ [y]_s = vy /\
  [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e x |--> X ** var_e y |--> Y ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  \B^nk * \S_{ nk } Y =m \S_{ nk } X * \S_{ nk } X {{ \S_{ nk } M }} /\ \S_{ nk } Y < \S_{ nk } M) **
 (fun s h => u2Z [i]_s = Z_of_nat ni /\ u2Z [n]_s = Z_of_nat nn /\
  [b2k]_s = vb2k /\ [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
  (var_e x \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 ** var_e l |--> L ** var_e b2k |--> B2K) s h /\
  flatten (map (bits (n:=32)) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj) {{ \S_{ nk } M }})).

move=> s h [h1 [h2 [Hdisj [Hunion [
[Y [len_Y [r_x [r_y [r_m [r_k [r_alpha [Hmem1 [Sum_Y Y_M]]]]]]]]]
[r_i [r_n [r_one' [r_l [r_L_ [r_32 [r_j [Hmem2 [Hbbs' [Hninn [Hnj32 [r_w [Hbbs [Hbbs'' Sum_X]]]]]]]]]]]]]]
]]]]].
exists Y; repeat (split; trivial).
rewrite (decompose_last_equiv _ X) HlenX.
move: {Hmem1 Hmem2}(assert_m.con_cons _ _ _ _ _ Hdisj Hmem1 Hmem2).
rewrite -Hunion => Hmem.
by assoc_comm Hmem.
eapply eqmod_trans.
exact: Sum_Y.
eapply eqmod_rewrite.
apply eqmod_sym; exact: Sum_X.
rewrite mulZC.
eapply eqmod_rewrite.
apply eqmod_sym; exact: Sum_X.
rewrite -ZpowerD addnn -mul2n -expnS -addnS; exact: eqmod_refl.

apply frame_rule_R.
- eapply mont_square_strict_init_triple => //.
  by abstract Uniq_uniq r0.
- by Inde_frame.
- move=> ?; by Inde_mult.

(**      mont_mul_strict_init k alpha y b2k x m one ext int_ Y_ B2K_ X_ M_ quot C t s_; *)

apply pull_out_exists => Y.

apply (hoare_prop_m.hoare_stren (!(fun s => size Y = nk) **
 (fun s h => u2Z [i]_s = Z_of_nat ni /\ size X = nk /\
  u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\
  [x]_s = vx /\ [y]_s = vy /\ [m]_s = vm /\ [b2k]_s = vb2k /\
  [alpha]_s = valpha /\ [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \B^nk * \S_{ nk } Y =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj.+1) {{ \S_{ nk } M }} /\ \S_{ nk } Y < \S_{ nk } M))).

move=> {HlenX} s h [Hri [HlenX [HlenY [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs' [Hninn [Hnj32 [Hrw [Hbbs [Hbbs'' [Sum_Y HSum_Y']]]]]]]]]]]]]]]]]]]]]].

exists heap.emp, h; repeat (split => //).
by map_tac_m.Disj.
by map_tac_m.Equal.

apply pull_out_bang => HlenY.

apply (hoare_prop_m.hoare_stren (fun s h => exists X,
 u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ u2Z [k]_s = Z_of_nat nk /\
 u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\ [y]_s = vy /\
 [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\ [l]_s = vl /\
 u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\ u2Z [thirtytwo]_s = Z_of_nat 32 /\
 u2Z [j]_s = Z_of_nat nj /\
 (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
 flatten (map (@bits 32) (take ni L)) =
 bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
 (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
 take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
 drop nj (bits vw) = bits.zeros (32 - nj) /\
 \B^nk * \S_{ nk } Y =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj.+1) {{ \S_{ nk } M }} /\ \S_{ nk } Y < \S_{ nk } M)).

move=> {HlenX} s h [Hri [HlenX [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs' [Hninn [Hnj32 [Hrw [Hbbs [Hbbs'' [Sum_Y Sum_Y']]]]]]]]]]]]]]]]]]]]].
by exists X.

apply while.hoare_seq with (fun s h => exists X, u2Z [i]_s = Z_of_nat ni /\
 size X = nk /\ u2Z [k]_s = Z_of_nat nk /\
 u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\ [y]_s = vy /\
 [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\
 [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
 u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
 (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
 flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
 (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
 take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
 drop nj (bits vw) = bits.zeros (32 - nj) /\
 \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj.+1) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M).

apply (hoare_prop_m.hoare_stren (!(fun s => \S_{ nk } Y < \S_{ nk } M) **
((fun s h => exists X, size X = nk /\
  [y]_s = vy /\ [b2k]_s = vb2k /\ [x]_s = vx /\ [m]_s = vm /\
  u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e y |--> Y ** var_e b2k |--> B2K ** var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h) **
 (fun s h => u2Z [i]_s = Z_of_nat ni /\ u2Z [n]_s = Z_of_nat nn /\
   [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
  (var_e l |--> L ** var_e y \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \B^nk * \S_{ nk } Y =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj.+1) {{ \S_{ nk } M}})))).

move=> {X HlenX} s h [X [Hri [HlenX [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs' [Hninn [Hnj32 [Hrw [Hbbs [Hbbs'' [Sum_Y Y_M]]]]]]]]]]]]]]]]]]]]]].

exists heap.emp, h; repeat (split; trivial).
by map_tac_m.Disj.
by map_tac_m.Equal.

have {Hmem}Hmem : ((var_e y |--> Y ** var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e b2k |--> B2K) **
    (var_e y \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32 ** var_e l |--> L)) s h.
  rewrite (decompose_last_equiv _ Y) HlenY in Hmem.
  by assoc_comm Hmem.
case: Hmem => h1 [h2 [Hdisj [Hunion [Hmem1 Hmem2]]]].
exists h1, h2; repeat (split; trivial).
exists X; repeat (split; trivial).
assoc_comm Hmem1.
by assoc_comm Hmem2.

apply pull_out_bang => Y_M.

apply hoare_prop_m.hoare_weak with ((fun s h => exists X, size X = nk /\ [y]_s = vy /\ [b2k]_s = vb2k /\
  [x]_s = vx /\ [m]_s = vm /\ u2Z [k]_s = Z_of_nat nk /\ [alpha]_s = valpha /\
  (var_e y |--> Y ** var_e b2k |--> B2K ** var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil) s h /\
  \B^nk * \S_{ nk } X =m \S_{ nk } Y * \S_{ nk } B2K {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M) **
 (fun s h => u2Z [i]_s = Z_of_nat ni /\ u2Z [n]_s = Z_of_nat nn /\
  [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
  (var_e l |--> L ** var_e y \+ int_e (Z2u 32 (Z_of_nat (4 * nk))) |~> int_e zero32) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \B^nk * \S_{ nk } Y =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj.+1) {{ \S_{ nk } M }})).

move=> {X HlenX} s h [h1 [h2 [Hdisj [Hunion [
[X [HlenX [r_y [r_one' [r_x [r_m [r_k [r_alpha [Hmem1 [Sum_X X_M]]]]]]]]]]
[r_i [r_n [r_l [r_L_ [r_32 [r_j [Hmem2 [Hbbs' [Hninn [Hnj32 [r_w [Hbbs [Hbbs'' Sum_Y]]]]]]]]]]]]]
]]]]].
exists X; repeat (split; trivial).
rewrite (decompose_last_equiv _ Y) HlenY.
move: {Hmem1 Hmem2}(assert_m.con_cons _ _ _ _ _ Hdisj Hmem1 Hmem2).
rewrite -Hunion => Hmem.
by assoc_comm Hmem.
eapply eqmod_trans; last exact: Sum_Y.
apply eqmod_sym in Sum_X.
rewrite mulZC in Sum_X.
move: (eqmod_rewrite _ _ _ _ _ HSumB2K1 Sum_X) => Htmp.
rewrite -Zpower_b_square -mulZA mulZC in Htmp.
apply eqmod_sym in Htmp.
rewrite mulZC in Htmp.
apply eqmod_reg_mult' in Htmp => //.
rewrite /Zbeta.
exact/Zis_gcd_sym/Zis_gcd_Zpower_odd.

apply frame_rule_R.
- eapply mont_mul_strict_init_triple; trivial.
  by abstract Uniq_uniq r0.
- by Inde_frame.
- move=> ?; by Inde_mult.

(**      lw w' zero16 x; *)

apply hoare_lw_back_alt'' with (fun s h => exists X vw nj,
  u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\ [y]_s = vy /\
  [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\ [l]_s = vl /\
  u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\ u2Z [thirtytwo]_s = Z_of_nat 32 /\
  u2Z [j]_s = Z_of_nat nj /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj.+1) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M /\
  [w']_s = X `32_ 0).

move=> {X HlenX} s h [X [Hri [HlenX [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [mem [Hbbs' [Hninn [Hnj32 [Hrw [Hbbs [Hbbs'' [Sum_X Sum_X']]]]]]]]]]]]]]]]]]]]]].

have Htmp : [ var_e x \+ int_e (sext 16 zero16) ]e_ s = [ var_e x ]e_ s.
  by rewrite /= sext_0 addi0.
destruct X as [|Xhd Xtl]; first by destruct nk.
exists Xhd; split.
rewrite /= !assert_m.conAE in mem.
move: mem; apply monotony => // h'.
exact: mapsto_ext.
rewrite /update_store_lw.
exists (Xhd :: Xtl), vw, nj.
repeat Reg_upd; repeat (split; trivial).
by Assert_upd.

(**      andi w' w' one16 ; *)

apply hoare_andi with (fun s h => exists X vw nj,
  u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\ [y]_s = vy /\
  [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\
  [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj.+1) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M /\
  [w']_s = X `32_ 0 `& one32).

move=> {X HlenX vw nj} s h [X [vw [nj [Hri [HlenX [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs' [Hninn [Hnj32 [Hrw [Hbbs [Hbbs'' [Sum_X [Sum_X' r_w']]]]]]]]]]]]]]]]]]]]]]]]].
rewrite /wp_andi.
repeat Reg_upd.
exists X, vw, nj; repeat (split; trivial).
by Assert_upd.
by rewrite r_w' zext_Z2u.

(**      sllv w' w' j ; *)

apply hoare_sllv with (fun s h => exists X vw nj,
  u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\ [y]_s = vy /\
  [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\
  [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\ [w]_s = vw /\
  take nj (bits vw) = bbs_fun_rec nj ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj (bits vw) = bits.zeros (32 - nj) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj.+1) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M /\
  [w']_s = (X `32_ 0 `& one32) `<< nj).

move=> {X HlenX vw nj} s h [X [vw [nj [Hri [HlenX [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs' [Hninn [Hnj32 [Hrw [Hbbs [Hbbs'' [Sum_X [Sum_X' Hrw']]]]]]]]]]]]]]]]]]]]]]]]].
rewrite /wp_sllv.
repeat Reg_upd.
exists X, vw, nj; repeat (split; trivial).
by Assert_upd.
have -> : u2Z ([j]_s `% 5) = Z_of_nat nj.
  rewrite u2Z_rem' //= Hrj (_ : 32 = Z_of_nat 32) //; exact/inj_lt/ltP.
by rewrite Hrw' Zabs2Nat.id.

(**      cmd_or w w w' ; *)

apply hoare_or with (fun s h => exists X vw nj,
  u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ u2Z [k]_s = Z_of_nat nk /\
  u2Z [n]_s = Z_of_nat nn /\ [x]_s = vx /\ [y]_s = vy /\
  [m]_s = vm /\ [b2k]_s = vb2k /\ [alpha]_s = valpha /\
  [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
  u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat nj /\
  (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
  flatten (map (@bits 32) (take ni L)) = bbs_fun_rec (ni * 32) (\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) (\S_{ nk } M) /\
  (ni < nn)%nat /\ (nj < 32)%nat /\
  take nj.+1 (bits vw) = bbs_fun_rec nj.+1 ((\S_{ nk } X0 ^^ 2 mod \S_{ nk } M) ^^ 2 ^ (ni * 32) mod \S_{ nk } M) (\S_{ nk } M) /\
  drop nj.+1 (bits vw) = bits.zeros (32 - nj.+1) /\
  \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni * 32 + nj.+1) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M /\
  [w]_s = vw).

move=> {X HlenX vw nj} s h [X [vw [nj [Hri [HlenX [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs' [Hninn [Hnj32 [Hrw [Hbbs [Hbbs'' [Sum_X [Sum_X' Hrw']]]]]]]]]]]]]]]]]]]]]]]]].
rewrite /wp_or.
repeat Reg_upd.
exists X, (int_or ((X `32_ 0 `& one32) `<< nj) vw), nj; repeat (split; trivial).
by Assert_upd.

rewrite bbs_fun_rec_cat0 -Hbbs [take]lock /= -!lock.
rewrite (take_nth true); last by rewrite size_bits.
rewrite mulZ1.
rewrite Zpower_exp_mod.
rewrite Zpower_b_square.
rewrite Zpower_exp_mod.
rewrite -expnD -expnS -addnS.
rewrite {1}bits_int_or (bits.take_or 32); last 2 first.
  by rewrite size_bits.
  by rewrite size_bits.
rewrite take_bits // (bits.orC nj); last 2 first.
  by rewrite /bits.zeros size_nseq.
  by rewrite size_take size_bits Hnj32.
rewrite bits.orl0; last first.
  by rewrite size_take size_bits Hnj32.
rewrite bits_int_or (bits.nth_or 32); last 2 first.
  exact: size_bits.
  exact: size_bits.
rewrite nth_bits //.
rewrite (drop_nth true) in Hbbs''; last by rewrite size_bits.
rewrite (_ : 32 - nj = (32 - nj.+1).+1)%nat in Hbbs''; last by rewrite -subSn.
rewrite /= in Hbbs''.
case: Hbbs'' => -> _.
rewrite bits.bit_or_false -(Zodd_bool_multi nk) //.
have Htmp : 0 < \S_{ nk } M by apply (@leZ_ltZ_trans (\S_{ nk } X)); [exact: min_lSum | exact Sum_X'].
apply eqmod_mod in Sum_X => //.
apply eqmod_inv in Sum_X; last 2 first.
  split => //; exact: min_lSum.
  exact/Z_mod_lt/Z.lt_gt.
by rewrite -Sum_X cats1.

rewrite bits_int_or (bits.drop_or 32); last 2 first.
  exact: size_bits.
  exact: size_bits.
rewrite drop_bits // (bits.orC (32 - nj.+1)); last 2 first.
  by rewrite /bits.zeros size_nseq.
  by rewrite size_drop size_bits.
rewrite bits.orl0 //; last by rewrite size_drop size_bits.
rewrite -add1n drop_addn drop1 Hbbs'' bits.tail_zeros; last by apply/ltP; ssromega.
by rewrite addnC subnDA // size_drop size_bits.
by rewrite -Hrw' Hrw int_orC.

(*      addiu j j one16); *)

apply hoare_addiu'.

move=> {X HlenX vw nj} s h [X [vw [nj [Hri [HlenX [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs' [Hninn [Hnj32 [Hbbs [Hbbs'' [Sum_X [Sum_X' Hrw]]]]]]]]]]]]]]]]]]]]]]]].
rewrite /wp_addiu.
repeat Reg_upd.
exists X, Y, vw, nj.+1.
repeat (split; trivial).
rewrite sext_Z2u // u2Z_add_Z2u // Hrj.
rewrite Z_S; ring.
apply (@ltZ_trans 33); [ | by []].
rewrite (_ : 33 = Z_of_nat 32 + 1) //; exact/ltZ_add2r/inj_lt/ltP.
by Assert_upd.

(**    sw w zero16 L_ ; *)

apply hoare_sw_back'' with (fun s h => exists X Y vw L,
 u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ size Y = nk /\
 size L = nn /\ u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\
 [x]_s = vx /\ [y]_s = vy /\ [m]_s = vm /\ [b2k]_s = vb2k /\
 [alpha]_s = valpha /\ [l]_s = vl /\ u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni /\
 u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat 32 /\
 (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
 flatten (map (@bits 32) (take ni.+1 L)) = bbs_fun_rec (ni.+1 * 32) (\S_{ nk } X0 ^^ 2 mod (\S_{ nk } M) mod (\S_{ nk } M)) (\S_{ nk } M) /\
 (ni < nn)%nat /\ [w]_s = vw /\
 \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni.+1 * 32) {{ \S_{ nk } M }} /\ \S_{ nk } X < \S_{ nk } M).

move=> s h [X [Y [vw [r_i [len_X [len_Y [r_k [r_n [r_x [r_y [r_m [r_b2k [r_alpha [r_l [r_L_ [r_32 [r_j [mem [Hbbs' [ni_nn [r_w [Hbbs [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]]].

have Htmp : [ var_e L_ \+ int_e (sext 16 zero16) ]e_ s =
  [ var_e l \+ int_e (Z2u 32 (Z_of_nat (4 * ni))) ]e_ s.
  rewrite /= sext_0 addi0; apply u2Z_inj.
  rewrite r_L_ u2Z_add_Z2u.
  by rewrite r_l inj_mult.
  exact: Zle_0_nat.
  rewrite r_l inj_mult [Z_of_nat 4]/= -Zbeta1E.
  apply/(ltZ_trans _ Hnl)/ltZ_add2l/ltZ_pmul2l => //; exact/inj_lt/ltP.

exists (int_e (nth zero32 L ni)).

Decompose_32 L ni L1 L2 HlenL1 HL'; last by rewrite HlenL.

rewrite HL' (decompose_equiv _ _ _ _ _ HlenL1) in mem.
do 3 Rotate mem.
(* rewrite !assert_m.conAE assert_m.conCE !assert_m.conAE assert_m.conCE !assert_m.conAE assert_m.conCE !assert_m.conAE in mem.*)
move: mem; apply monotony => // ht.
exact: mapsto_ext.
apply currying => h' H'; simpl app in H'.
exists X, Y, vw, (upd_nth L ni vw); repeat (split; trivial).
exact: size_upd_nth.
rewrite HL' upd_nth_cat HlenL1 // subnn /= (decompose_equiv _ _ _ _ _ HlenL1).
rewrite cat0s in H'.
assoc_comm H'.
exact: mapsto_ext H'.

rewrite (take_nth zero32); last by rewrite (@size_upd_nth _ nn).
rewrite nth_upd_nth; last by rewrite HlenL.
rewrite -cats1 map_cat flatten_cat. simpl flatten.
rewrite mulnC bbs_fun_rec_cat -(mulnC ni).
by rewrite cats0 Hbbs take_upd_nth Hbbs' !Zmod_mod.

clear L HlenL.

(**    addiu L_ L_ four16 ; *)

apply hoare_addiu with (fun s h => exists X Y vw L,
 u2Z [i]_s = Z_of_nat ni /\ size X = nk /\ size Y = nk /\
 size L = nn /\ u2Z [k]_s = Z_of_nat nk /\ u2Z [n]_s = Z_of_nat nn /\
 [x]_s = vx /\ [y]_s = vy /\ [m]_s = vm /\ [b2k]_s = vb2k /\
 [alpha]_s = valpha /\ [l]_s = vl /\
 u2Z [L_]_s = u2Z vl + 4 * Z_of_nat ni.+1 /\
 u2Z [thirtytwo]_s = Z_of_nat 32 /\ u2Z [j]_s = Z_of_nat 32 /\
 (var_e x |--> X ++ zero32 :: nil ** var_e m |--> M ++ zero32 :: nil ** var_e l |--> L ** var_e y |--> Y ++ zero32 :: nil ** var_e b2k |--> B2K) s h /\
 flatten (map (@bits 32) (take ni.+1 L)) = bbs_fun_rec (ni.+1 * 32) (\S_{ nk } X0 ^^ 2 mod (\S_{ nk } M)) (\S_{ nk } M) /\
 (ni < nn)%nat /\ [w]_s = vw /\
 \S_{ nk } X =m \S_{ nk } X0 ^^ 2 ^ (ni.+1 * 32) {{\S_{ nk } M}} /\ \S_{ nk } X < \S_{ nk } M).

move=> s h [X [Y [vw [L [Hri [HlenX [HlenY [HlenL [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs [Hninn [Hrw [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]]]].
rewrite /wp_addiu.
repeat Reg_upd.
exists X, Y, vw, L; repeat (split; trivial).

rewrite sext_Z2u // u2Z_add_Z2u // HrL_.
rewrite Z_S; ring.
rewrite -Zbeta1E; apply: (leZ_ltZ_trans _ Hnl).
  rewrite -addZA; apply leZ_add2l.
  rewrite -{2}(mulZ1 4) -mulZDr -Z_S.
  apply leZ_pmul => //; exact/inj_le/leP.
by Assert_upd.
by rewrite Zmod_mod in Hbbs.

(**    addiu i i one16). *)

apply hoare_addiu'.

move=> s h [X [Y [vw [L [Hri [HlenX [HlenY [HlenL [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [HrL_ [Hr32 [Hrj [Hmem [Hbbs' [Hninn [Hrw [Sum_X X_M]]]]]]]]]]]]]]]]]]]]]]]].
rewrite /wp_addiu.
repeat Reg_upd.
exists ni.+1, L, X, Y; repeat (split; trivial).
rewrite sext_Z2u // u2Z_add_Z2u // Hri.
by rewrite Z_S.
rewrite -Zbeta1E; apply: (ltZ_trans _ Hnl).
  rewrite -(add0Z (Z_of_nat ni + 1)).
  apply leZ_lt_add; first exact: min_u2Z.
  rewrite -Z_S mulZC -(mulZ1 (Z_of_nat ni.+1)).
  apply ltZ_pmul => //.
  exact/inj_le/leP.
by Assert_upd.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Epsilon Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext ssrnat_ext seq_ext.
Require Import machine_int multi_int uniq_tac.
Require listbit.
Import MachineInt.
Require Import sgoto compile.
Require Import encode_decode.
Require Import mips_seplog mips_contrib mips_tactics mapstos.
Require Import mont_mul_strict_prg bbs_prg bbs_triple bbs_termination.

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

(** [IMPLEMENTATION] interface as used in #<a href="http://staff.aist.go.jp/reynald.affeldt/coqdev/BBS_Asm_CryptoProof.html">BBS_Asm_CryptoProof.v</a>#. *)

(** The following signature summarizes what has to be proved of the implementation
    in Assembly of BBS.  It is instantiated in the module
    Implem below. *)

Module Type IMPLEMENTATION.

Definition label := nat.

Parameter state : Type.

Definition lstate := (label * state)%type.

(** [encode nn nk modu seed] is the initial state built from the requested length [nn] in
    32-bits words, the size [nk] in 32-bits words of the buffers used to store the seed and
    the modulus, the modulus [modu], and the seed [seed], *)

Parameter encode : nat -> nat -> Z -> Z -> state.

(** [decode s] is the pseudorandom list of booleans extracted from the final state [s]. *)

Parameter decode : state -> list bool.

(** Syntax of Assembly: *)

Parameter scode : Type.

(** The big-step operational semantics of %\cite{saabasuustalu2007}%#[Saabas&Uustalu2007]#: *)

Parameter exec_sgoto : scode -> option lstate -> option lstate -> Prop.

(** The assembly code for BBS: *)

Parameter bbs_asm : scode.

(** Restrictions imposed by the implementation of [bbs_asm]: *)

Definition Restrictions (nn nk : nat) (modu seed : Z) : Prop :=
  0 < modu /\ modu < \B^nk /\ Zodd modu /\
  0 <= seed /\ seed < modu /\
  4 * (Z_of_nat (4 * nk + nn + 2)%nat) < \B^1.

(** Termination and determinism of [bbs_asm]: *)

Parameter exec_bbs_asm : forall nn nk modu seed, Restrictions nn nk modu seed ->
  { s_f : state |
    exec_sgoto bbs_asm (Some (O, encode nn nk seed modu)) (Some (240, s_f)) /\
    forall s', exec_sgoto bbs_asm (Some (O, encode nn nk seed modu)) s' ->
    s' = Some (240, s_f) }%nat.

(** [bbs_fun] is a generalization of [BBS.bbs] with relaxed types (see file file ZArith_ext.v).
    The assembly code [bbs_asm] implements [bbs_fun]: *)

Parameter bbs_semop : forall nn nk modu seed, Restrictions nn nk modu seed ->
  forall s_f,
    exec_sgoto bbs_asm (Some (O, encode nn nk seed modu)) (Some (240%nat, s_f)) ->
    decode s_f = bbs_fun (nn * 32) seed modu.

End IMPLEMENTATION.

(** [encode]/[decode] functions, lemmas for correctness and termination for BBS.
To be used to instantiate the [IMPLEMENTATION] interface (see at the end of this file). *)

Module Import compile_m := Compile WMIPS_Hoare.
Import sgoto_hoare_m.
Import sgoto_m.
Import goto_deter_m.

Local Open Scope sgoto_scope.

Section bbs.

(** Restrictions imposed by the implementation of [bbs_asm] *)

Hypothesis nk : nat.

Hypothesis modu : Z.
Hypothesis Hmodu : 0 < modu.
Hypothesis Hmodu' : modu < \B^nk.
Hypothesis Hoddmodu : Zodd modu.

Hypothesis seed : Z.
Hypothesis Hseed : 0 <= seed.
Hypothesis Hseedmodu : seed < modu.

Hypothesis nn : nat.
Hypothesis Hcond : 4 * Z_of_nat (4 * nk + nn + 2) < \B^1.

(** A series of technical lemmas just to help instantiating the Separation Logic triple of BBS. *)

Lemma inv_mod_prop (m : int 32) :
  Zodd (u2Z m) -> u2Z m * inv_mod_beta (u2Z m) =m -1 {{ \B^1 }}.
Proof.
move=> Hm.
rewrite /inv_mod_beta.
case: euclid_rec => u v d Heq Hgcd.
rewrite (Z_div_mod_eq u _ (Z.lt_gt _ _ (Zbeta_gt0 1))) in Heq.
move: (Zis_gcd_Zpower_odd 32 _ Hm); rewrite -/(\B^1); move/Zis_gcd_sym => Hgcd'.
case: (Zis_gcd_uniqueness_apart_sign _ _ _ _ Hgcd Hgcd') => Hd.
- rewrite Hd Zone_pos.
  case/boolP : (u == 0) => [/eqP | ] Hu0.
  + rewrite Hu0 Zmod_0_l Hd /= in Heq.
    move: (Zbeta1_1 v) => ?; contradiction.
  + exists (v + u2Z m * (u / \B^1) + u2Z m).
    rewrite (_ : -1 = - (1)) // -Hd -Heq; ring.
- rewrite Hd /=.
  exists (- v - u2Z m * (u / \B^1)).
  rewrite (_ : -1 = - (1)) // -Hd -Heq; ring.
Qed.

Lemma inv_mod_prop' (m : int 32) : Zodd (u2Z m) -> 0 <= inv_mod_beta (u2Z m) < \B^1.
Proof.
move=> Hm.
rewrite /inv_mod_beta.
case: euclid_rec => u v d Heq Hgcd.
rewrite (Z_div_mod_eq u _ (Z.lt_gt _ _ (Zbeta_gt0 1))) in Heq.
move: (Zis_gcd_Zpower_odd 32 _ Hm); rewrite -/(\B^1); move/Zis_gcd_sym => Hgcd'.
case: (Zis_gcd_uniqueness_apart_sign _ _ _ _ Hgcd Hgcd') => Hd.
- rewrite Hd Zone_pos.
  move: (Z_mod_lt u _ (Z.lt_gt _ _ (Zbeta_gt0 1))) => W.
  case: ifPn => Hu0.
  - split; [exact: leZZ | exact: expZ_gt0].
  - suff Humod : u mod \B^1 <> 0 by lia.
    move=> Humod.
    move: (Humod) => Humod'.
    apply Zmod_divide in Humod'; last lia.
    case: Humod' => q Hq.
    rewrite Humod Hq Z_div_mult // addZ0 in Heq.
    subst d.
    have {}Heq : (q * u2Z m + v) * \B^1 = 1 by rewrite -Heq; ring.
    move: (Zbeta1_1 (q * u2Z m + v)) => Heq'.
    contradiction.
- rewrite Hd Zle_imp_le_bool //.
  apply Z_mod_lt; exact/Z.lt_gt/expZ_gt0.
Qed.

Lemma Halpha : u2Z ((Z2ints 32 nk modu) `32_ 0) *
  u2Z (Z2u 32 (inv_mod_beta (u2Z ((Z2ints 32 nk modu) `32_ 0)))) =m -1 {{ \B^1 }}.
Proof.
rewrite Z2uK //.
- apply/inv_mod_prop/(@Zodd_lSum _ _ nk).
  rewrite lSum_Z2ints_pos //; split => //; exact/ltZW.
- apply/inv_mod_prop'/(@Zodd_lSum _ _ nk).
  rewrite lSum_Z2ints_pos //; split => //; exact/ltZW.
Qed.

Lemma HlenX0 : size (Z2ints 32 nk seed) = nk.
Proof. by rewrite size_Z2ints. Qed.

Lemma HlenB2K : size (Z2ints 32 nk ((\B^nk ^^ 2) mod (\S_{ nk } (Z2ints 32 nk modu)))) = nk.
Proof. by rewrite size_Z2ints. Qed.

Lemma HlenM : size (Z2ints 32 nk modu) = nk.
Proof. by rewrite size_Z2ints. Qed.

Lemma HlenY : size (Z2ints 32 nk 0) = nk.
Proof. by rewrite size_Z2ints. Qed.

Lemma Hvl : u2Z (Z2u 32 (4 * Z_of_nat (2 * nk + 2))) = 4 * (Z_of_nat (2 * nk + 2)).
Proof.
rewrite Z2uK // -Zbeta1E.
move: Hcond => ?.
omegaz.
(*move: Hcond. rewrite !inj_plus !mulZDr.
simpl Z_of_nat => ?; lia.*)
Qed.

Lemma Hnl : u2Z (Z2u 32 (4 * Z_of_nat (2 * nk + 2))) + 4 * Z_of_nat nn < \B^1.
Proof.
move: Hcond. rewrite Hvl => ?.
omegaz.
(*move: Hcond. rewrite Hvl 2!inj_plus !inj_mult !mulZDr inj_plus inj_mult.
simpl Z_of_nat => ?; lia.*)
Qed.

Lemma Hnx : u2Z zero32 + 4 * Z_of_nat nk.+1 < \B^1.
Proof.
move: Hnl.
rewrite Hvl Z2uK // => ?.
omegaz.
(*move: Hnl.
rewrite Hvl Z2uK // Z_S 2!inj_plus !mulZDr.
simpl Z_of_nat => ?; lia.*)
Qed.

Lemma HSumX0SumM : \S_{ nk } (Z2ints 32 nk seed) < \S_{ nk } (Z2ints 32 nk modu).
Proof.
rewrite !lSum_Z2ints_pos //.
split; by [exact/ltZW | ].
split; by [ | exact: (@ltZ_trans modu)].
Qed.

Lemma HSumB2KSumM :
  \S_{ nk } (Z2ints 32 nk (\B^nk ^^ 2 mod (\S_{ nk } (Z2ints 32 nk modu)))) <
  \S_{ nk } (Z2ints 32 nk modu).
Proof.
rewrite !lSum_Z2ints_pos //.
- exact (proj2 (Z_mod_lt (\B^nk ^^ 2) modu (Z.lt_gt _ _ Hmodu))).
- split; by [exact/ltZW | ].
- split.
  + exact (proj1 (Z_mod_lt (\B^nk ^^ 2) _ (Z.lt_gt _ _ Hmodu))).
  + apply (@ltZ_trans modu); last by [].
    exact (proj2 (Z_mod_lt (\B^nk ^^ 2) modu (Z.lt_gt _ _ Hmodu))).
- split; by [exact/ltZW | ].
Qed.

Lemma HSumB2K : \S_{ nk } (Z2ints 32 nk (\B^nk ^^ 2 mod (\S_{ nk } (Z2ints 32 nk modu)))) =m \B^nk ^^ 2 {{ \S_{ nk } (Z2ints 32 nk modu) }}.
Proof.
rewrite lSum_Z2ints_pos.
- apply eqmod_sym, eqmod_mod.
  rewrite lSum_Z2ints_pos // -ZbetaE; lia.
  exact: eqmod_refl.
- split; first exact/Zmod_le/min_lSum.
  rewrite -ZbetaE lSum_Z2ints_pos //.
  + apply (@ltZ_trans modu); last by [].
    exact: (proj2 (Z_mod_lt (\B^nk ^^ 2) modu (Z.lt_gt _ _ Hmodu))).
  + rewrite -ZbetaE; lia.
Qed.

Lemma HoddM' : Zodd (\S_{ nk } (Z2ints 32 nk modu)).
Proof. rewrite lSum_Z2ints_pos //. split => //; exact/ltZW. Qed.

Lemma Hvy : u2Z (Z2u 32 (4 * Z_of_nat (2 * nk + nn + 2))) = 4 * (Z_of_nat (2 * nk + nn + 2)).
Proof.
rewrite Z2uK // -Zbeta1E.
move: Hcond. rewrite !inj_plus !mulZDr.
move=> ?; omegaz.
(*simpl Z_of_nat=> ?; lia.*)
Qed.

Lemma Hny : u2Z (Z2u 32 (4 * Z_of_nat (2 * nk + nn + 2))) + 4 * Z_of_nat nk.+1 < \B^1.
Proof.
move: Hcond. rewrite Hvy Z_S !inj_plus.
simpl Z_of_nat => H.
destruct nk as [|nk'].
- move: Hmodu'.
  rewrite (_ : \B^0 = 1) // => Hmodu''.
  exfalso.
  lia.
- rewrite ?Z_S in H *; by ssromega.
Qed.

(** Let us be given 25 registers... *)

Variables i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w : reg.

(** We instantiate the Separation Logic triple of BBS, this gives us a proof of functional correctness. *)
Definition bbs_triple_spec
  (Hset : uniq (i :: L_ :: l :: n :: j :: thirtytwo :: k :: alpha :: x :: y ::
    m :: one :: ext :: int_ :: X_ :: Y_ :: M_ :: quot :: C_ :: t :: s_ :: b2k ::
    B2K_ :: w' :: w :: r0 :: nil)) :=
  bbs_triple _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hset nk
  (Z2u 32 (inv_mod_beta (u2Z ((Z2ints 32 nk modu) `32_ 0)))) (Z2ints 32 nk modu)
  Halpha nn (Z2ints 32 nn 0) (size_Z2ints nn 32 0) (Z2ints 32 nk seed) (Z2ints 32 nk 0)
  (Z2ints 32 nk ((\B^nk ^^ 2) mod (\S_{ nk } (Z2ints 32 nk modu)))) HlenX0 HlenB2K
  HlenM HlenY _ _ (Z2u 32 (4 * Z_of_nat nk.+1)) (Z2u 32 (4 * Z_of_nat (3 * nk + nn + 3))) _ Hny Hnx Hnl HSumX0SumM
  HSumB2KSumM HSumB2K HoddM'.

(** [encode nn nk modu seed] is the initial state built from the requested length [nn] in 32-bits words, the size [nk] in 32-bits words of the buffer used to store the seed and the modulus, the modulus [modu], and the seed [seed]. *)

Definition encode (nn nk : nat) (seed modu : Z) : state :=
  let nx := O in
  let nm := nk.+1 in
  let nl := (2 * nk + 2)%nat in
  let ny := (2 * nk + nn + 2)%nat in
  let nb2k := (3 * nk + nn + 3)%nat in
  (store.upd k (Z2u 32 (Z_of_nat nk))
  (store.upd n (Z2u 32 (Z_of_nat nn))
  (store.upd x (Z2u 32 (4 * Z_of_nat nx))
  (store.upd m (Z2u 32 (4 * Z_of_nat nm))
  (store.upd l (Z2u 32 (4 * Z_of_nat nl))
  (store.upd y (Z2u 32 (4 * Z_of_nat ny))
  (store.upd b2k (Z2u 32 (4 * Z_of_nat nb2k))
  (store.upd alpha (Z2u 32 (inv_mod_beta (u2Z ((Z2ints 32 nk modu) `32_ 0))))
  (store.upd thirtytwo (Z2u 32 32) (store.null_multiplier nil))))))))) ,
  list2heap nx (Z2ints 32 nk seed) \U heap.sing (nx + nk) zero32 \U
  list2heap nm (Z2ints 32 nk modu) \U heap.sing (nm + nk) zero32 \U
  list2heap nl (Z2ints 32 nn 0) \U
  list2heap ny (Z2ints 32 nk 0) \U heap.sing (ny + nk) zero32 \U
  list2heap nb2k (Z2ints 32 nk (\B^nk ^^ 2 mod (\S_{ nk } (Z2ints 32 nk modu)))))%nat.

(** [decode s] is the pseudorandom list of booleans extracted from the final state [s]. *)

Definition decode (st : state) : list bool :=
  let: (s, h) := st in
  let: nn := '| u2Z [n]_s | in
  flatten (map (@bits 32) (heap2list '| u2Z ([ l ]_s `>> 2) | nn h)).

Lemma decode_heap s h L : (var_e l |--> L ** TT) s h ->
  u2Z ([ var_e l ]e_ s) + 4 * Z_of_nat (size L) < \B^1 ->
  u2Z [ n ]_s = Z_of_nat (size L) ->
  decode (s, h) = flatten (map (@bits 32) L).
Proof.
move=> H Hfit gpr_n.
rewrite /decode.
do 2 f_equal.
case: H => h1 [h2 [Hdisj [Hunion [H _]]]].
move: {H}(mapstos_inv_list2heap _ _ _ _ H Hfit) => H.
rewrite Hunion H /= heap2list_list2heap_union; last 2 first.
  by rewrite gpr_n Zabs2Nat.id.
  by rewrite /= -H.
by rewrite heap2list2heap // gpr_n Zabs2Nat.id.
Qed.

(** We prove a specialized version of the Separation Logic triple of BBS with the [encode]/[decode] functions. *)

(* TODO: move? *)
Lemma disj_not_In_for_tac : forall {A : Type} (n : A) l,
  seq_ext.disj (n :: nil) l -> ~ List.In n l.
Proof.
move=> a n0 l0 H.
by move/((proj1 (H n0)) (or_introl _ (refl_equal n0))).
Qed.

Ltac disj_heap :=
  match goal with
    | |- heap.sing ?a _ # (list2heap ?b ?l) =>
      apply heap.disj_sym; disj_heap
    | |- (list2heap ?b ?l) # heap.sing ?a _ =>
      apply heap.disj_sing_R ;
      apply/seq_ext.inP ;
      rewrite ?dom_list2heap ?size_Z2ints ?heap.dom_sing ?size_nseq /=;
      apply disj_not_In_for_tac;
      apply/disP; by dis_iota_tac
    | |- list2heap ?a ?l # list2heap ?b ?k =>
      apply disj_list2heap ;
        rewrite ?dom_list2heap ?size_Z2ints ?size_nseq /=; apply/disP; by dis_iota_tac
    | |- heap.sing ?a _ # heap.sing ?b _ =>
      apply heap.disj_sing; ssromega
  end.

Lemma bbs_triple_encode_decode :
  uniq (i :: L_ :: l :: n :: j :: thirtytwo :: k :: alpha :: x :: y :: m ::
    one :: ext :: int_ :: X_ :: Y_ :: M_ :: quot :: C_ :: t :: s_ :: b2k :: B2K_ ::
    w' :: w :: r0 :: nil) ->
  {{ fun s h => encode nn nk seed modu = (s, h) }}
  bbs i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w
  {{ fun s h => decode (s, h) = bbs_fun (nn * 32) seed modu }}.
Proof.
move=> Hset.
apply: (while.hoare_conseq _ _ _ expr_b (fun eb s => eval_b eb (fst s)) hoare0 _ _ _ _ _ _ _ (bbs_triple_spec Hset)).
- move=> s h [L [X [Y0 [HlenL [HlenX [HlenY0 [Hrk [Hrn [Hrx [Hry [Hrm [Hrb2k [Hralpha [Hrl [Hr32 [Hmem Hbbs]]]]]]]]]]]]]]]].
  rewrite lSum_Z2ints_pos // in Hbbs; last by rewrite -ZbetaE; lia.
  rewrite lSum_Z2ints_pos // in Hbbs; last by rewrite -ZbetaE; lia.
  rewrite /bbs_fun Zpower_b_square -Hbbs.
  apply decode_heap.
  + by assoc_comm Hmem.
  + rewrite [eval _ _]/= Hrl Z2uK //.
    * move: (Hcond) => ?; by omegaz.
    * move: (Hcond) => ?; by rewrite -Zbeta1E; omegaz.
  by rewrite HlenL.
- rewrite /encode /while.entails => s h.
  rewrite [Zmult]lock [Z_of_nat]lock [store.upd]lock.
  case=> Hstore Hmem.
  rewrite -!lock in Hstore Hmem *.
  rewrite -{-10}Hstore.
  repeat Reg_upd.
  move: (Hcond) => Hcond'.
  rewrite Z2uK; last by rewrite -Zbeta1E; omegaz.
  split; first by [].
  rewrite Z2uK; last by rewrite -Zbeta1E; omegaz.
  split; first by [].
  rewrite mulZ0.
  split; first by [].
  split; first by f_equal; omegaz.
  split; first by reflexivity.
  split; first by f_equal; omegaz.
  split; first by reflexivity.
  split; first by f_equal; omegaz.
  split; first by rewrite Z2uK.
  rewrite -Hmem.
  do 3 rewrite decompose_last_equiv size_Z2ints.
  rewrite !assert_m.conAE -!heap.unionA.
  apply assert_m.con_cons.
    - apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      by disj_heap.
    - apply (mapstos_ext (int_e zero32) s).
      + rewrite ![eval _ _]/= -Hstore.
        repeat Reg_upd.
        by rewrite mulZ0.
      + apply mapstos_list2heap.
        by rewrite Z2uK.
        by rewrite size_Z2ints // Z2uK //; omegaz.
  apply assert_m.con_cons.
    - apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      by disj_heap.
    - exists nk; split; last by [].
      rewrite [eval _ _]/= -Hstore.
      repeat Reg_upd.
      rewrite mulZ0 add0i Z2uK //.
      by omegaz.
      by rewrite -Zbeta1E; omegaz.
  apply assert_m.con_cons.
    - apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      by disj_heap.
    - apply mapstos_list2heap.
      + rewrite Z_S [Zmult]lock /= -Hstore.
        repeat Reg_upd.
        rewrite -!lock Z2uK //.
        by omegaz.
        by rewrite -Zbeta1E; omegaz.
      + rewrite size_Z2ints [eval _ _]/= -Hstore.
        repeat Reg_upd.
        rewrite Z2uK //.
        by omegaz.
        by rewrite -Zbeta1E; omegaz.
  apply assert_m.con_cons.
    - apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      by disj_heap.
    - exists (2 * nk + 1)%nat; split.
      + rewrite [eval _ _]/= -Hstore.
        repeat Reg_upd.
        rewrite u2Z_add Z2uK //.
        * rewrite Z2uK //.
          by omegaz.
          by rewrite -Zbeta1E; omegaz.
        * by rewrite -Zbeta1E; omegaz.
        * rewrite Z2uK //.
          by rewrite -Zbeta1E; omegaz.
        * by rewrite -Zbeta1E; omegaz.
        * by rewrite -Zbeta1E; omegaz.
      + f_equal; ssromega.
  apply assert_m.con_cons.
    - apply heap.disjhU; first by disj_heap.
      apply heap.disjhU; first by disj_heap.
      by disj_heap.
    - apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat (2 * nk + 2)))) s).
      + rewrite [Zmult]lock /= -Hstore.
        repeat Reg_upd.
        by rewrite -!lock.
      + apply mapstos_list2heap.
        rewrite Z2uK //.
        by rewrite -Zbeta1E; omegaz.
        rewrite Z2uK //.
        by rewrite size_nseq; omegaz.
        by rewrite -Zbeta1E; omegaz.
  apply assert_m.con_cons.
    - apply heap.disjhU; first by disj_heap.
      by disj_heap.
    - apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat (2 * nk + nn + 2)))) s).
      + rewrite [Zmult]lock /= -Hstore.
        repeat Reg_upd.
        by rewrite -!lock.
      + apply mapstos_list2heap.
        rewrite Z2uK //.
        by rewrite -Zbeta1E; omegaz.
        rewrite Z2uK //.
        by rewrite size_nseq; omegaz.
        by rewrite -Zbeta1E; omegaz.
  apply assert_m.con_cons.
    - by disj_heap.
    - exists (3 * nk + nn + 2)%nat.
      rewrite [Zmult]lock /= -Hstore.
      repeat Reg_upd.
      rewrite -!lock.
      split.
      + rewrite u2Z_add_Z2u.
        rewrite Z2uK //.
        by omegaz.
        by rewrite -Zbeta1E; omegaz.
        by omegaz.
        rewrite Z2uK //.
        by rewrite -Zbeta1E; omegaz.
        by rewrite -Zbeta1E; omegaz.
      - f_equal; ssromega.
apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat (3 * nk + nn + 3)))) s).
- rewrite [Zmult]lock /= -Hstore.
  repeat Reg_upd.
  by rewrite -!lock.
  - apply mapstos_list2heap.
  + rewrite Z2uK // -Zbeta1E.
    (*; omegaz TODO: used to work*)
    destruct nk => //.
    move: Hmodu'. rewrite (_ : \B^0 = 1) // => Hmodu''.
    exfalso. lia.
    rewrite ?inj_plus ?Z_S in Hcond' *; lia.
    rewrite Z2uK //.
    * rewrite size_Z2ints; by omegaz.
    * destruct nk => //.
      move: Hmodu'. rewrite (_ : \B^0 = 1) // => Hmodu''.
      exfalso. lia.
      rewrite ?inj_plus ?Z_S in Hcond' *.
      rewrite -Zbeta1E; by omegaz.
Qed.

Ltac repeat_disj_heap :=
  match goal with
    | |- _ # (_ \U _) =>
      apply heap.disjhU; [by disj_heap | repeat_disj_heap]
    | |- _ # _ =>
      by disj_heap
  end.

Lemma bbs_termination' :
  uniq (i :: L_ :: l :: n :: j :: thirtytwo :: k :: alpha :: x :: y :: m ::
    one :: ext :: int_ :: X_ :: Y_ :: M_ :: quot :: C_ :: t :: s_ :: b2k ::
    B2K_ :: w' :: w :: r0 :: nil) ->
  { s_f : state |
    Some (encode nn nk seed modu) --
    bbs i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w --->
    Some s_f }.
Proof.
move=> Hset.
move Hencode : (encode _ _ _ _) => [s0 h0].
apply (hoare_prop_m.termi _ _ _ (bbs_triple_spec Hset)).
move=> s h H.
apply bbs_termination => //.
rewrite /encode in Hencode.
rewrite [Zmult]lock [Z_of_nat]lock [store.upd]lock in Hencode. (*TODO: we need to protect all that because case simplifies it...*)
case: Hencode => Hstore Hmem.
rewrite -!lock in Hstore Hmem.
move: (Hcond) => Hcond'.
rewrite -{-10}Hstore.
repeat Reg_upd.
split.
  rewrite Z2uK //; last by rewrite -Zbeta1E; omegaz.
split.
  rewrite Z2uK //; last by rewrite -Zbeta1E; omegaz.
split; first by rewrite mulZ0.
split.
  f_equal; by omegaz.
split; first by [].
split.
  f_equal; by omegaz.
split; first by [].
split; first by f_equal; omegaz.
split; first by rewrite Z2uK.
rewrite -Hmem.
do 3 rewrite decompose_last_equiv size_Z2ints.
rewrite !assert_m.conAE -!heap.unionA.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - apply (mapstos_ext (int_e zero32) s0).
    + rewrite -Hstore /=.
      by repeat Reg_upd.
    + apply mapstos_list2heap.
      by rewrite Z2uK.
      rewrite Z2uK // size_Z2ints; omegaz.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - exists nk; split; last by [].
    rewrite -Hstore [eval _ _]/=.
    repeat Reg_upd.
    rewrite add0i Z2uK //.
    by omegaz.
    by rewrite -Zbeta1E; omegaz.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat nk.+1))) s0).
    + rewrite -Hstore Z_S [Zmult]lock /=.
      repeat Reg_upd.
      by rewrite -!lock.
    + apply mapstos_list2heap.
      rewrite Z2uK //.
      rewrite -Zbeta1E; by omegaz.
      rewrite Z2uK //.
      rewrite size_Z2ints; by omegaz.
      rewrite -Zbeta1E; by omegaz.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - exists (2 * nk + 1)%nat; split.
    + rewrite -Hstore [Zmult]lock [Z_of_nat]lock /=.
      repeat Reg_upd.
      rewrite -!lock u2Z_add Z2uK //.
      rewrite Z2uK //.
      by omegaz.
      rewrite -Zbeta1E; by omegaz.
      rewrite -Zbeta1E; by omegaz.
      rewrite Z2uK //.
      rewrite -Zbeta1E; by omegaz.
      rewrite -Zbeta1E; by omegaz.
      rewrite -Zbeta1E; by omegaz.
    + f_equal; ssromega.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat (2 * nk + 2)))) s0).
    + rewrite -Hstore [Zmult]lock /=.
      repeat Reg_upd.
      by rewrite -!lock.
    + apply mapstos_list2heap.
      rewrite Z2uK //.
      rewrite -Zbeta1E; by omegaz.
      rewrite Z2uK //.
      rewrite size_nseq; by omegaz.
      rewrite -Zbeta1E; by omegaz.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat (2 * nk + nn + 2)))) s0).
    rewrite -Hstore [Zmult]lock /=.
    repeat Reg_upd.
    by rewrite -!lock.
    apply mapstos_list2heap.
    rewrite Z2uK //.
    rewrite -Zbeta1E; by omegaz.
    rewrite Z2uK //.
    rewrite size_nseq; by omegaz.
    rewrite -Zbeta1E; by omegaz.
apply assert_m.con_cons.
  - by repeat disj_heap.
  - exists (3 * nk + nn + 2)%nat.
    rewrite -Hstore [Zmult]lock /=.
    repeat Reg_upd.
    rewrite -!lock.
    split.
    + rewrite u2Z_add_Z2u.
      rewrite Z2uK //.
      omegaz.
      rewrite -Zbeta1E; omegaz.
      exact: Zle_0_nat.
      rewrite Z2uK //.
      rewrite -Zbeta1E; by omegaz.
      rewrite -Zbeta1E; by omegaz.
    + f_equal; ssromega.
apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat (3 * nk + nn + 3)))) s0).
rewrite -Hstore [Zmult]lock /=.
repeat Reg_upd.
by rewrite -!lock.
apply mapstos_list2heap.
- rewrite Z2uK //.
  destruct nk => //.
  + move: Hmodu'. rewrite (_ : \B^0 = 1) // => Hmodu''.
    exfalso. lia.
  + rewrite ?inj_plus ?Z_S in Hcond' *. rewrite -Zbeta1E; by omegaz.
- rewrite Z2uK //.
  rewrite size_Z2ints; omegaz. (* TODO: rewrite -Zbeta1_Zpower2; omegaz. used to work *)
  destruct nk => //.
  + move: Hmodu'. rewrite (_ : \B^0 = 1) // => Hmodu''.
    exfalso. lia.
  + rewrite ?inj_plus ?Z_S in Hcond' *. rewrite -Zbeta1E; by omegaz.
Qed.

(** From the termination of BBS written with while-loops, we derive the termination of BBS written with jumps. *)

Lemma exec_bbs_asm : uniq (i :: L_ :: l :: n :: j :: thirtytwo :: k :: alpha :: x ::
  y :: m :: one :: ext :: int_ :: X_ :: Y_ :: M_ :: quot :: C_ :: t :: s_ :: b2k ::
  B2K_ :: w' :: w :: r0 :: nil) ->
  { s_f : state |
    Some (O, encode nn nk seed modu) >-
    compile_f O (bbs i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_
      quot C_ t s_ b2k B2K_ w' w) ---> Some (240%nat, s_f) }.
Proof.
move=> Hset.
case: (bbs_termination' Hset) => s_f Hs_f.
exists s_f.
lapply (preservation_of_evaluations
  (bbs i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w)
  (encode nn nk seed modu) O
  (compile_f O
    (bbs i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w))
  s_f 240%nat).
move/(_ Hs_f).
exact.
apply: compile_f_compile.
by vm_compute.
Qed.

(** The assembly code [bbs_asm] implements [bbs_fun]. *)

Lemma bbs_semop s_f :
  uniq (i :: L_ :: l :: n :: j :: thirtytwo :: k :: alpha :: x :: y :: m ::
    one :: ext :: int_ :: X_ :: Y_ :: M_ :: quot :: C_ :: t :: s_ :: b2k ::
    B2K_ :: w' :: w :: r0 :: nil) ->
  Some (O, encode nn nk seed modu) >-
  compile_f O (bbs i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_
    quot C_ t s_ b2k B2K_ w' w) ---> Some (240%nat, s_f) ->
  decode s_f = bbs_fun_rec (nn * 32) ((seed * seed) mod modu) modu.
Proof.
move=> Hset.
move Hs0 : (encode _ _ _ _ ) => [s0 h0].
move Hs_f : s_f => [sf hf].
move: (bbs_triple_spec Hset) => Hbbs_triple_spec_while.
move: {Hbbs_triple_spec_while}(preservation_hoare _ _ _ Hbbs_triple_spec_while O
  (compile_f O
    (bbs i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w))
  240%nat) => Hbbs_triple_spec_sau.
lapply Hbbs_triple_spec_sau; clear Hbbs_triple_spec_sau.

move/hoare_sgoto_sound => Htriple_bbs.
move: {Htriple_bbs}(Htriple_bbs O s0 h0) => Htriple_bbs.
have Hinit0 : O = O /\ u2Z [k]_s0 = Z_of_nat nk /\
                u2Z [n]_s0 = Z_of_nat nn /\
                [x]_s0 = zero32 /\
                [y]_s0 = Z2u 32 (4 * Z_of_nat (2 * nk + nn + 2)) /\
                [m]_s0 = Z2u 32 (4 * Z_of_nat nk.+1) /\
                [b2k]_s0 = Z2u 32 (4 * Z_of_nat (3 * nk + nn + 3)) /\
                [alpha]_s0 = Z2u 32 (inv_mod_beta (u2Z ((Z2ints 32 nk modu) `32_ 0))) /\
                [l]_s0 = Z2u 32 (4 * Z_of_nat (2 * nk + 2)) /\
                u2Z [thirtytwo]_s0 = Z_of_nat 32 /\
                (var_e x |--> Z2ints 32 nk seed ++ zero32 :: nil **
                  var_e m |--> Z2ints 32 nk modu ++ zero32 :: nil **
                var_e l |--> Z2ints 32 nn 0 **
                var_e y |--> Z2ints 32 nk 0 ++ zero32 :: nil **
                var_e b2k
                |--> Z2ints 32 nk (\B^nk ^^ 2 mod \S_{ nk } (Z2ints 32 nk modu))) s0
                  h0.
  rewrite /encode in Hs0.
  rewrite Z_S [Zmult]lock [store.upd]lock in Hs0 *.
  case: Hs0 => Hstore Hmem.
  rewrite -!lock in Hstore Hmem *.
  move: (Hcond) => Hcond'.
  rewrite -{-10}Hstore.
  repeat Reg_upd.
  split; first by reflexivity.
  split.
    rewrite Z2uK //; rewrite -Zbeta1E; by omegaz.
  split.
    rewrite Z2uK //; rewrite -Zbeta1E; by omegaz.
  split; first by rewrite mulZ0.
  split.
    by f_equal; omegaz.
  split; first by [].
  split; first by f_equal; omegaz.
  split; first by [].
  split; first by f_equal; omegaz.
  split; first by rewrite Z2uK.
  rewrite -Hmem.
do 3 rewrite decompose_last_equiv size_Z2ints.
rewrite !assert_m.conAE -!heap.unionA.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - apply (mapstos_ext (int_e zero32) s0).
    rewrite /= -Hstore.
    repeat Reg_upd.
    by rewrite mulZ0.
    apply mapstos_list2heap.
    by rewrite Z2uK.
    rewrite Z2uK // size_Z2ints; by omegaz.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - exists nk; split; last by [].
    rewrite [eval _ _]/= -Hstore.
    repeat Reg_upd.
    rewrite mulZ0 add0i Z2uK //.
    by omegaz.
    rewrite -Zbeta1E; by omegaz.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat nk.+1))) s0).
    rewrite Z_S [Zmult]lock /= -Hstore.
    repeat Reg_upd.
    by rewrite -!lock.
    apply mapstos_list2heap.
    rewrite Z2uK //.
    rewrite -Zbeta1E; by omegaz.
    rewrite Z2uK //.
    rewrite size_Z2ints; by omegaz.
    rewrite -Zbeta1E; by omegaz.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - exists (2 * nk + 1)%nat; split.
    + rewrite [eval _ _]/= -Hstore.
      repeat Reg_upd.
      rewrite u2Z_add Z2uK //.
      rewrite Z2uK //.
      by omegaz.
      rewrite -Zbeta1E; by omegaz.
      rewrite -Zbeta1E; by omegaz.
      rewrite Z2uK //.
      rewrite -Zbeta1E; by omegaz.
      rewrite -Zbeta1E; by omegaz.
      rewrite -Zbeta1E; by omegaz.
    + f_equal; ssromega.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat (2 * nk + 2)))) s0).
    rewrite [Zmult]lock /= -Hstore.
    repeat Reg_upd.
    by rewrite -!lock.
    apply mapstos_list2heap.
    rewrite Z2uK //.
    rewrite -Zbeta1E; by omegaz.
    rewrite Z2uK //.
    rewrite size_nseq; by omegaz.
    rewrite -Zbeta1E; by omegaz.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat (2 * nk + nn + 2)))) s0).
    rewrite [Zmult]lock /= -Hstore.
    repeat Reg_upd.
    by rewrite -!lock.
    apply mapstos_list2heap.
    rewrite Z2uK //.
    rewrite -Zbeta1E; by omegaz.
    rewrite Z2uK //.
    rewrite size_nseq; by omegaz.
    rewrite -Zbeta1E; by omegaz.
apply assert_m.con_cons.
  - by repeat_disj_heap.
  - exists (3 * nk + nn + 2)%nat.
    rewrite -Hstore [Zmult]lock /=.
    repeat Reg_upd.
    rewrite -!lock.
    split.
    + rewrite u2Z_add_Z2u.
      rewrite Z2uK //.
      by omegaz.
      rewrite -Zbeta1E; by omegaz.
      exact: Zle_0_nat.
      rewrite Z2uK //.
      rewrite -Zbeta1E; by omegaz.
      rewrite -Zbeta1E; by omegaz.
    + f_equal; ssromega.
apply (mapstos_ext (int_e (Z2u 32 (4 * Z_of_nat (3 * nk + nn + 3)))) s0).
rewrite [Zmult]lock /= -Hstore.
repeat Reg_upd.
by rewrite -!lock.
apply mapstos_list2heap.
rewrite Z2uK //. (* TODO: rewrite -Zbeta1E; omegaz. used to work *)
- destruct nk.
  + move: Hmodu'. rewrite (_ : \B^0 = 1) // => Hmodu''.
    exfalso. lia.
  + rewrite ?inj_plus ?Z_S in Hcond' *.
    rewrite -Zbeta1E; by omegaz.
    rewrite Z2uK //.
    rewrite size_Z2ints; by omegaz. (* TODO: rewrite -Zbeta1E; omegaz. used to work *)
- destruct nk.
  + move: Hmodu'. rewrite (_ : \B^0 = 1) // => Hmodu''.
    exfalso. lia.
  + rewrite ?inj_plus ?Z_S in Hcond' *.
    rewrite -Zbeta1E; by omegaz.

case: {Htriple_bbs Hinit0}(Htriple_bbs Hinit0) => Htriple_bbs_no_error Htriple_bbs Hexec_bbs.
case: {Htriple_bbs}(Htriple_bbs _ _ _ Hexec_bbs) => Hlabel [Lf [Xf [Yf [HlenLf [HlenXf [HlenYf [Hrkf [Hrnf [Hrxf [Hryf [Hrm_f [Hrb2kf [Hralphaf [Hrlf [Hr32f [Hmemf Hbbsf]]]]]]]]]]]]]]]].
rewrite lSum_Z2ints_pos // in Hbbsf; last first.
  split; by [ | exact: (@ltZ_trans modu)].
rewrite -Zpower_b_square in Hbbsf.
rewrite lSum_Z2ints_pos // in Hbbsf; last by split; [exact/ltZW | ].
rewrite -Hbbsf.
apply decode_heap.
by assoc_comm Hmemf.
rewrite [eval _ _]/= Hrlf Hvl HlenLf.
rewrite -Hvl.
exact Hnl.
by rewrite HlenLf.
exact: compile_f_compile.
Qed.

End bbs.

(** Instantiation of the [IMPLEMENTATION] interface used in #<a href="http://staff.aist.go.jp/david.nowak/toolbox/BBS_Asm_CryptoProof.html">BBS_Asm_CryptoProof.v</a># *)

Module Implem : IMPLEMENTATION.

Definition label : Set := compile_m.sgoto_hoare_m.sgoto_m.goto_deter_m.goto_m.label.

Definition state : Type := mips_cmd.state.

Definition lstate := (label * state)%type.

Definition l := reg_t0.
Definition n := reg_t1.
Definition thirtytwo := reg_t2.
Definition k := reg_t3.
Definition alpha := reg_t4.
Definition x := reg_t5.
Definition y := reg_t6.
Definition m := reg_t7.
Definition b2k := reg_t8.

Definition encode := encode l n thirtytwo k alpha x y m b2k.

Definition decode := decode l n.

Definition scode := compile_m.sgoto_hoare_m.sgoto_m.scode.

Definition exec_sgoto := compile_m.sgoto_hoare_m.sgoto_m.exec_sgoto.

Definition w := reg_t9.
Definition w' := reg_s0.
Definition B2K_ := reg_s1.
Definition s_ := reg_s2.
Definition t := reg_s3.
Definition C_ := reg_s4.
Definition quot := reg_s5.
Definition M_ := reg_s6.
Definition Y_ := reg_s7.
Definition X_ := reg_a0.
Definition int_ := reg_a1.
Definition ext := reg_a2.
Definition one := reg_a3.
Definition j := reg_v0.
Definition L_ := reg_v1.
Definition i := reg_at.

Definition bbs_asm :=
  compile_m.compile_f O (bbs i L_ l n j thirtytwo k alpha x y m one ext int_ X_ Y_ M_ quot C_ t s_ b2k B2K_ w' w).

Definition Restrictions (nn nk : nat) (modu seed : Z) : Prop :=
  0 < modu /\ modu < \B^nk /\ Zodd modu /\
  0 <= seed /\ seed < modu /\
  4 * Z_of_nat (4 * nk + nn + 2) < \B^1.

Lemma exec_bbs_asm nn nk modu seed : Restrictions nn nk modu seed ->
  { s_f : state |
    exec_sgoto bbs_asm (Some (O, encode nn nk seed modu)) (Some (240, s_f)) /\
    forall s',
    exec_sgoto bbs_asm (Some (O, encode nn nk seed modu)) s' -> s' = Some (240, s_f)}%nat.
Proof.
move=> [Hmodu [Hmodu' [Hmodu'' [Hseed [Hseed' Hcond]]]]].
have Hset : uniq (i :: L_ :: l :: n :: j :: thirtytwo :: k :: alpha :: x :: y ::
  m :: one :: ext :: int_ :: X_ :: Y_ :: M_ :: quot :: C_ :: t :: s_ :: b2k ::
  B2K_ :: w' :: w :: r0 :: nil) by rewrite //=.
move: (exec_bbs_asm _ _ Hmodu Hmodu' Hmodu'' _ Hseed Hseed' _ Hcond
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hset) => [s' Hs'].
exists s'.
split; [by [] | move=> s'' Hexec].
have Hwf : compile_m.sgoto_hoare_m.sgoto_m.wellformed bbs_asm.
  eapply compile_m.compile_wellformed.
  apply compile_m.compile_f_compile.
  rewrite /bbs_asm.
  reflexivity.
eapply determinacy.
- exact: Hwf.
- exact: Hexec.
- by [].
Qed.

Lemma bbs_semop nn nk modu seed : Restrictions nn nk modu seed ->
  forall s_f,
  exec_sgoto bbs_asm (Some (O, encode nn nk seed modu)) (Some (240%nat, s_f)) ->
  decode s_f = bbs_fun (nn * 32) seed modu.
Proof.
move=> [Hmodu [Hmodu' [Hmodu'' [Hseed [Hseed' Hcond]]]]] s_f Hexec.
have Hset : uniq (i :: L_ :: l :: n :: j :: thirtytwo :: k :: alpha :: x ::
  y :: m :: one :: ext :: int_ :: X_ :: Y_ :: M_ :: quot :: C_ :: t :: s_ ::
  b2k :: B2K_ :: w' :: w :: r0 :: nil) by rewrite //=.
apply (bbs_semop _ _ Hmodu Hmodu' Hmodu'' _ Hseed Hseed' _ Hcond
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s_f Hset).
by rewrite /exec_sgoto /bbs_asm in Hexec.
Qed.

End Implem.

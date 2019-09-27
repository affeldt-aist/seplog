(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext seq_ext ssrnat_ext.
Require Import machine_int.
Import MachineInt.
Require while.

(**
  This file provides:
  - a definition of MIPS registers
  - a module for "stores" (register files)
  - a module for a language for expression built out of registers
  - a module fot the language of assertions of Separation logic
  Here, modules are used as name-spaces.
*)

Declare Scope mips_expr_scope.
Declare Scope heap_scope.
Declare Scope mips_assert_scope.

(** General purpose registers *)
Inductive reg : Set :=
| r0 : reg (* $0: always return zero, writes are ignored *)
| reg_at : reg (* $1: assembler temporary *)
| reg_v0 : reg (* $2,$3: values return by subroutine *)
| reg_v1 : reg
| reg_a0 : reg (* $4-$7: first four parameters for a subroutine *)
| reg_a1 : reg
| reg_a2 : reg
| reg_a3 : reg
| reg_t0 : reg (* $8-$15,$24,$25: subroutines may use w.o. saving *)
| reg_t1 : reg
| reg_t2 : reg
| reg_t3 : reg
| reg_t4 : reg
| reg_t5 : reg
| reg_t6 : reg
| reg_t7 : reg
| reg_t8 : reg
| reg_t9 : reg
| reg_s0 : reg (* $16-$23: must be restored by the subroutine *)
| reg_s1 : reg
| reg_s2 : reg
| reg_s3 : reg
| reg_s4 : reg
| reg_s5 : reg
| reg_s6 : reg
| reg_s7 : reg
| reg_k0 : reg (* $26,$27: reserved for use by interrupt/trap handler *)
| reg_k1 : reg
| reg_gp : reg (* $28: global pointer *)
| reg_sp : reg (* $29: stack pointer *)
| reg_fp : reg (* $30: frame pointer *)
| reg_ra : reg. (* $31: used by the subroutine calling instructions for the return address *)

Definition regP (r1 r2 : reg) : bool :=
  match (r1, r2) with
    | (r0, r0) => true
    | (reg_at, reg_at) => true
    | (reg_v0, reg_v0) => true
    | (reg_v1, reg_v1) => true
    | (reg_a0, reg_a0) => true
    | (reg_a1, reg_a1) => true
    | (reg_a2, reg_a2) => true
    | (reg_a3, reg_a3) => true
    | (reg_t0, reg_t0) => true
    | (reg_t1, reg_t1) => true
    | (reg_t2, reg_t2) => true
    | (reg_t3, reg_t3) => true
    | (reg_t4, reg_t4) => true
    | (reg_t5, reg_t5) => true
    | (reg_t6, reg_t6) => true
    | (reg_t7, reg_t7) => true
    | (reg_t8, reg_t8) => true
    | (reg_t9, reg_t9) => true
    | (reg_s0, reg_s0) => true
    | (reg_s1, reg_s1) => true
    | (reg_s2, reg_s2) => true
    | (reg_s3, reg_s3) => true
    | (reg_s4, reg_s4) => true
    | (reg_s5, reg_s5) => true
    | (reg_s6, reg_s6) => true
    | (reg_s7, reg_s7) => true
    | (reg_k0, reg_k0) => true
    | (reg_k1, reg_k1) => true
    | (reg_gp, reg_gp) => true
    | (reg_sp, reg_sp) => true
    | (reg_fp, reg_fp) => true
    | (reg_ra, reg_ra) => true
    | _ => false
  end.

Lemma regP_eq : forall n m, regP n m -> n = m.
Proof. by case; case. Qed.

Lemma regP_refl : forall n, regP n n.
Proof. by case. Qed.

Lemma eqregP : Equality.axiom regP.
Proof. move=> n m. apply: (iffP idP); move: n m; by case; case. Qed.

Canonical Structure reg_eqMixin := EqMixin eqregP.
Canonical Structure reg_eqType := Eval hnf in EqType _ reg_eqMixin.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.

Module store.

Definition var := reg.
Definition val := int 32.
(** register file *)
Definition rf := list (reg * int 32).
Definition acx_size := 8%nat.
(** The SmartMIPS multiplier is a set of registers called ACX, HI, and
LO that has been designed to enhance cryptographic computations. HI
and LO are 32 bits long; ACX is only known to be at least 8 bits
long. We formalize the multiplier as an abstract date type
%\coqdocvar{m}%#m# with three lookup functions %\coqdocvar{acx}%#acx#,
%\coqdocvar{hi}%#hi#, and %\coqdocvar{lo}%#lo# that return respectively
a machine integer of length at list 8 bits and machine integers of
length 32 bits. *)
Definition t := (rf * (int acx_size * (int 32 * int 32)))%type.
(* Definition dom :=
  r0 :: reg_at :: reg_v0 :: reg_v1 :: reg_a0 :: reg_a1 :: reg_a2 :: reg_a3 ::
  reg_t0   :: reg_t1 :: reg_t2 :: reg_t3 :: reg_t4 :: reg_t5 :: reg_t6 :: reg_t7 ::
  reg_t8   :: reg_t9 :: reg_s0 :: reg_s1 :: reg_s2 :: reg_s3 :: reg_s4 :: reg_s5 ::
  reg_s6   :: reg_s7 :: reg_k0 :: reg_k1 :: reg_gp :: reg_sp :: reg_fp :: reg_ra :: nil.

Lemma In_dom : forall r : reg, In r dom. by rewrite /dom; case => //=; tauto. Qed.*)

Lemma acx_size_min : (8 <= acx_size)%nat. Proof. done. Qed.

Definition acx (s : t) := match s with (_, (a, _)) => a end.
Definition hi (s : t) := match s with (_, (_, (b, _))) => b end.
Definition lo (s : t) := match s with (_, (_, (_, c))) => c end.

Fixpoint get' (r : reg) (s : rf) : val :=
  match s with
    | nil => zero32
    | (r', i) :: tl => if r == r' then i else get' r tl
  end.

Definition get r (s : t) : val :=
  match s with (s, _) => if r == r0 then zero32 else get' r s end.

Fixpoint upd' (r : reg) (i : int 32) (s : rf) : rf :=
  match s with
    | nil => (r, i) :: nil
    | (r',i') :: tl => if r == r' then (r,i) :: tl else (r',i') :: upd' r i tl
  end.

Definition upd r i (s : t) : t :=
  match s with
    (s, m) => if r == r0 then (s, m) else (upd' r i s, m)
  end.

(*Lemma upd_store_mult : forall r v s m, r <> r0 -> upd r v (s, m) = (upd' r v s, m).
Proof. move=> r v s mu. move/eqP. move/negbTE => /= -> //. Qed.*)

Lemma get_upd_p : forall st x y z, x <> y -> get' x (upd' y z st) = get' x st.
Proof.
elim => [x y z H /= | [a b] l Hst x y z Hxy /=].
- suff : x == y = false by move=> ->.
  by apply/negP; move/eqP.
- have Hxy' : x == y = false by apply/negP; move/eqP.
  case/boolP : (x == a) => H1.
  + case/boolP : (y == a) => H2.
    * rewrite /=.
      have {H1 H2}H : x == y by move/eqP : H2 => ->.
      by rewrite H in Hxy'.
    * by rewrite /= H1.
  + move/negbTE in H1.
    case/boolP : (y == a) => H2; last move/negbTE in H2.
    * by rewrite /= Hxy' // H1.
    * rewrite /= H1; by apply Hst.
Qed.

Lemma get_upd x y z st : x <> y -> get x (upd y z st) = get x st.
Proof.
case: st => [st mu] Hxy.
rewrite /get /upd.
case/boolP : (x == r0) => H1.
- by case/boolP : (y == r0).
- case/boolP : (y == r0) => H2 //.
  by rewrite get_upd_p.
Qed.

Lemma get_upd_p' : forall st w z , get' w (upd' w z st) = z.
Proof.
elim=> //=.
- move=> *; by rewrite eq_refl.
- move=> [a b] /= l Hst w z.
  case: ifP => H1.
  + by rewrite /= eq_refl.
  + rewrite /= H1; by apply Hst.
Qed.

Lemma get_upd' x z : forall st, x <> r0 -> get x (upd x z st) = z.
Proof.
move=> [st mu] H.
rewrite /get /upd.
have -> : x == r0 = false by apply/negP; move/eqP.
by apply get_upd_p'.
Qed.

Lemma upd_upd_p : forall st x z z', upd' x z' (upd' x z st) = upd' x z' st.
Proof.
elim => [x z z' /= | [hd hd'] tl IH x z z' /=].
- by rewrite eqxx.
  case: ifP => Htmp.
  + by rewrite /= eqxx.
  + by rewrite /= Htmp /= IH.
Qed.

Lemma upd_upd_eq x z z' : forall st, upd x z' (upd x z st) = upd x z' st.
Proof.
move=> [st mu].
rewrite /upd.
case/boolP : (x == r0) => H1 //.
by rewrite upd_upd_p.
Qed.

(** r0 always evaluates to zero *)
Lemma get_r0 : forall s, get r0 s = zero32.
Proof. by move=> [s mu]. Qed.

(** r0 is invariant *)
Lemma upd_r0 : forall s x, upd r0 x s = s.
Proof. by move=> [s mu] x. Qed.

Lemma acx_upd : forall r v s, acx (upd r v s) = acx s.
Proof.  move=> r v [s [a [h l]]] /=; by case: ifP. Qed.

Lemma hi_upd : forall r v s, hi (upd r v s) = hi s.
Proof. move=> r v [s [a [h l]]] /=; by case: ifP. Qed.

Lemma lo_upd : forall r v s, lo (upd r v s) = lo s.
Proof. move=> r v [s [a [h l]]] /=; by case: ifP. Qed.

(** mthi *)
Definition mthi_op (x : int 32) (s : t) : t :=
  match s with (s, (a, (b, c))) => (s, (a, (x, c))) end.

Lemma acx_mthi_op: forall s a, acx (mthi_op a s) = acx s.
Proof. move=> [s [a [l h] ]] n //=. Qed.

Lemma hi_mthi_op: forall m a, hi (mthi_op a m) = a.
Proof. move=> [s [a [l h] ]] n //=. Qed.

Lemma lo_mthi_op : forall m a, lo (mthi_op a m) = lo m.
Proof. move=> [_ [a [l h] ]] n //=. Qed.

(** mtlo *)
Definition mtlo_op (x : int 32) (m : t) : t :=
  match m with (s, (a, (b, c))) => (s, (a, (b, x))) end.

Lemma acx_mtlo_op: forall m a, acx (mtlo_op a m) = acx m.
Proof. move=> [_ [a [l h] ]] n //=. Qed.

Lemma hi_mtlo_op: forall m a, hi (mtlo_op a m) = hi m.
Proof. move=> [_ [a [l h] ]] n //=. Qed.

Lemma lo_mtlo_op: forall m a, lo (mtlo_op a m) = a.
Proof. move=> [_ [a [l h] ]] n //=. Qed.

(** interpretation of the multiplier as an unsigned integer *)
Definition utoZ s :=
  let acx_reg := acx s in
  let (hi_reg, lo_reg) := (hi s, lo s) in
  u2Z acx_reg * \B^2 + u2Z hi_reg * \B^1 + u2Z lo_reg.

Lemma utoZ_def: forall s, utoZ s = u2Z (lo s) + u2Z (hi s) * \B^1 + u2Z (acx s) * \B^2.
Proof. move=> [a [l h] ] /=. rewrite /utoZ /=. by ring. Qed.

Lemma utoZ_upd : forall r v s, utoZ (upd r v s) = utoZ s.
Proof. move=> r v [s [a [h l]]] /=; by case: ifP. Qed.

Lemma utoZ_pos mu : 0 <= utoZ mu.
Proof.
rewrite utoZ_def.
move: (min_u2Z (lo mu)) => H.
have H' : 0 <= u2Z (hi mu) * \B^1 by apply mulZ_ge0 => //; exact/min_u2Z.
have H'' : 0 <= u2Z (acx mu) * \B^2 by apply mulZ_ge0 => //; exact/min_u2Z.
do 2 apply addZ_ge0 => //.
Qed.

Lemma utoZ_acx_beta2 : forall m, utoZ m < \B^2 -> acx m = Z2u acx_size 0.
Proof.
move=> [s [a [h l] ]] H /=.
rewrite /utoZ /= in H.
have [H0 | H0] : u2Z a = 0 \/ u2Z a > 0 by move: (min_u2Z a) => H'; by omega.
- apply u2Z_inj; by rewrite Z2uK.
- have H1 : \B^2 <= u2Z a * \B^2.
    apply (@leZ_trans (1 * \B^2)); first by rewrite mul1Z.
    apply leZ_pmul2r => //; omega.
  have H2 : 0 <= u2Z h * \B^1 by apply mulZ_ge0 => //; exact/min_u2Z.
  move: (min_u2Z l) => ?.
  have [//] : ~ (u2Z a * \B^2 + u2Z h * \B^1 + u2Z l < \B^2) by omega.
Qed.

Lemma hi_zero : forall m, utoZ m < \B^1 -> hi m = Z2u 32 0.
Proof.
move=> [s [a [h l] ]] H /=.
rewrite /utoZ /= in H.
have [H0 | H0] : u2Z h = 0 \/ u2Z h > 0 by move: (min_u2Z h) => H'; by omega.
- apply u2Z_inj; by rewrite Z2uK.
- have ? : 0 <= u2Z a * \B^2 by apply mulZ_ge0 => //; exact/min_u2Z.
  have ? : \B^1 <= u2Z h * \B^1.
    apply (@leZ_trans (1 * \B^1)); first by rewrite mul1Z.
    apply leZ_pmul2r => //; omega.
  move: (min_u2Z l) => ?.
  have Habsurd : ~ (u2Z a * \B^2 + u2Z h * \B^1 + u2Z l < \B^1) by omega.
  contradiction.
Qed.

Lemma acxhi_zero  mu : utoZ mu < \B^1 -> utoZ mu = u2Z (lo mu).
Proof.
move=> H.
have [H1 H2] : acx mu = Z2u acx_size 0 /\ hi mu = Z2u 32 0.
  split; last exact: hi_zero.
  apply utoZ_acx_beta2; exact: (@ltZ_trans (\B^1)).
move: mu H H1 H2.
move=> [a [h l] ] /= H H1 H2.
by rewrite /utoZ /= H1 H2 /= !Z2uK.
Qed.

Lemma utoZ_lo_beta1 : forall m, utoZ m < \B^1 ->
  acx m = Z2u acx_size 0 /\ hi m = Z2u 32 0 /\ utoZ m = u2Z (lo m).
Proof.
move=> mu H; split.
apply utoZ_acx_beta2.
apply (@ltZ_trans (\B^1)) => //.
split; by [apply hi_zero | apply acxhi_zero].
Qed.

Lemma lo_remainder': forall m l (a : int l), (l = acx_size + 32 + 32)%nat ->
  utoZ m = u2Z a -> lo m = a `% 32.
Proof.
move=> [s [i0 [i1 i2] ]] /= l a Hl H.
rewrite utoZ_def /= in H.
have H1 : u2Z a = u2Z ((i0 `|| i1) `|| i2).
  rewrite 2!u2Z_concat -H Zbeta1E ZbetaE /=; ring.
subst l.
apply u2Z_inj in H1.
by rewrite H1 (rem_concat (i0 `|| i1) i2).
Qed.

Lemma lo_remainder : forall m l (a : int l), (l <= acx_size + 32 + 32)%nat ->
  utoZ m = u2Z a -> lo m = a `% 32.
Proof.
move=> mu l a H H'.
rewrite (lo_remainder' mu _ (zext ((acx_size + 32 + 32) - l) a)).
- apply u2Z_inj.
  by rewrite u2Z_rem_zext.
- move: acx_size_min => H''.
  ssromega.
- by rewrite u2Z_zext.
Qed.

Definition multi_null (s : t) := utoZ s = 0.

Definition null_multiplier (s : rf) : t := (s, (Z2u acx_size 0, (zero32, zero32))).

Lemma multi_null_utoZ : forall s, multi_null s -> utoZ s = 0.
Proof. rewrite //=. Qed.

Lemma utoZ_multi_null : forall m, utoZ m = 0 -> multi_null m.
Proof. rewrite //=. Qed.

Lemma multi_null_upd : forall r v s, multi_null (upd r v s) = multi_null s.
Proof. move=> r v [s [a [h l]]] /=; by case: ifP. Qed.

Lemma multi_null_lo : forall m, multi_null m -> lo m = Z2u 32 0.
Proof.
move=> [s [a [h l]]] /=.
rewrite /multi_null /utoZ /= => H.
apply u2Z_inj.
rewrite Z2uK //.
have ? : 0 <= u2Z a * \B^2 by apply mulZ_ge0 => //; exact/min_u2Z.
have ? : 0 <= u2Z h * \B^1 by apply mulZ_ge0 => //; exact/min_u2Z.
move: (min_u2Z l) => ?; omega.
Qed.

(** maddu *)
Definition maddu_op (p : int (2 * 32)) (m : t) : t :=
  match m with
    (s, m') =>
  let acx_reg := acx m in
  let hi_reg := hi m in
  let lo_reg := lo m in
    let sum := acx_reg `|| (hi_reg `|| lo_reg) in
      let new_sum := zext 8 p `+ sum in
        let lo_reg' := new_sum `% 32 in
      	  let sum' := shr_shrink 32 new_sum in
      	    let hi_reg' := sum' `% 32 in
      	      let acx_reg' := shr_shrink 32 sum' in
      	        (s, (acx_reg', (hi_reg', lo_reg')))
  end.

Lemma maddu_upd : forall a r v s, maddu_op a (upd r v s) = upd r v (maddu_op a s).
Proof. move=> A r v [s [a0 [h l]]] /=; by case: ifP. Qed.

Lemma concat_acx_hilo (a : int acx_size) (b : int (2 * 32)) :
  u2Z (a `|| b) = u2Z a * \B^2 + u2Z b.
Proof. by rewrite u2Z_concat. Qed.

Lemma utoZ_maddu : forall m a, utoZ m < \B^2 * (2 ^^ acx_size - 1) ->
  utoZ (maddu_op a m) = u2Z a + utoZ m.
Proof.
move=> [accu [ h l ] ] a H /=; move: H.
rewrite /utoZ /acx /hi /lo /maddu_op => H.
rewrite (_ : \B^2 = \B^1 * \B^1) //.
rewrite mulZA -mulZDl (@u2Z_shr_shrink 40 _ 32) //.
rewrite (@u2Z_shr_shrink 72 _ 32) //.
rewrite [Zbeta]lock /= -lock u2Z_add.
- by rewrite (u2Z_zext 8) concat_acx_hilo (@u2Z_concat 32) -ZbetaD !addZA.
- rewrite (u2Z_zext 8) concat_acx_hilo (@u2Z_concat 32) !addZA.
  move: (max_u2Z a) => H'.
  rewrite mulZBr mulZ1 in H.
  move: (expZ_ge1 acx_size) => H''.
  apply (@ltZ_leZ_trans (u2Z a + \B^2 * 2 ^^ acx_size - u2Z a)).
  + move: (ltZ_add _ _ _ _ H' H).
    by rewrite 2!addZA Zminus_plus.
  + by rewrite Zminus_plus.
Qed.

Definition multu_op (p : int (2 * 32)) (s : t) : t :=
  match s with (lst, m') =>
    let lo' := p `% 32 in
    let hi' := shr_shrink 32 p in
    (lst, (Z2u acx_size 0, (hi', lo')))
  end.

Lemma utoZ_multu : forall p m, utoZ (multu_op p m) = u2Z p.
Proof.
move=> p [a [h l]] /=.
rewrite /multu_op /utoZ /acx Z2uK // Zbeta1E.
by move: (@u2Z_shr_shrink (2 * 32) p 32 erefl).
Qed.

(** The %\coqdocvar{mflhxu}%#mflhxu# instruction performs a division by
%\ensuremath{2^{32}}%#2^32#, whose remainder is put in a
general-purpose register and whose quotient is left in the multiplier.
The corresponding hardware circuitry is essentially a shift: it puts
the contents of LO into some general-purpose register, puts the contents
of HI into LO, and zeroes ACX. *)
Definition mflhxu_op m :=
  match m with
  | (s, m') => let (acx_reg, hi_reg) := (acx m, hi m) in (s, (Z2u acx_size 0, (zext 24 acx_reg, hi_reg)))
  end.

Lemma mflhxu_upd : forall r v s, mflhxu_op (upd r v s) = upd r v (mflhxu_op s).
Proof. move=> r v [s [a0 [h l]]] /=; by case: ifP. Qed.

Lemma hi_mflhxu_op : forall m, u2Z (hi (mflhxu_op m)) = u2Z (zext (32 - acx_size) (acx m)).
Proof. by move=> [i0 [ i1 i2 ]]. Qed.

Lemma lo_mflhxu_op : forall m, lo (mflhxu_op m) = hi m.
Proof. by move=> [i0 [ i1 i2 ]]. Qed.

Lemma acx_mflhxu_op : forall m, acx (mflhxu_op m) = Z2u acx_size 0.
Proof. by move=> [i0 [ i1 i2 ]]. Qed.

(** The decimal values of the multiplier before and after %\coqdocvar{mflhxu}%#mflhxu# are related as follows:*)
Lemma mflhxu_utoZ : forall m, utoZ m = utoZ (mflhxu_op m) * \B^1 + u2Z (lo m).
Proof.
move=> [s [acx_reg [hi_reg lo_reg] ]] /=.
rewrite /mflhxu_op /= /utoZ /=.
rewrite -(@u2Z_zext 24 acx_size acx_reg).
move: (ZbetaD 1 1) => H.
rewrite H.
congr (_ + _).
rewrite mulZDl.
congr (_ + _).
by rewrite mulZDl Z2uK // [Zbeta]lock /= -lock mulZA.
Qed.

Lemma mflhxu_beta2_utoZ : forall m, utoZ m < \B^2 -> utoZ (mflhxu_op m) < \B^1.
Proof.
move=> [a [h l] ] /= H.
rewrite /mflhxu_op /=.
move: (utoZ_acx_beta2 _ H) => H0.
rewrite /= in H0.
rewrite H0.
have H1 : zext 24 (Z2u acx_size 0) = Z2u 32 0.
  apply u2Z_inj; by rewrite u2Z_zext !Z2uK.
rewrite /utoZ /= H1 !Z2uK //= Zbeta1E.
by apply max_u2Z.
Qed.

Lemma mflhxu_kbeta1_utoZ : forall m k, utoZ m < \B^1 * k -> utoZ (mflhxu_op m) < k.
Proof.
move=> mu.
destruct k.
- rewrite mulZ0.
  move: mu; move => [s [a [ h l]]] H.
  rewrite utoZ_def /= in H.
  have H' : u2Z l + u2Z h * \B^1 + u2Z a * \B^2 >= 0.
    have H1 :  0 <= u2Z h * \B^1 by apply mulZ_ge0 => //; exact/min_u2Z.
    have H2 : 0 <= u2Z a * \B^2 by apply mulZ_ge0 => //; exact/min_u2Z.
    move: (min_u2Z l) => ?; omega.
  contradiction.
- move: mu; move => [s [a [ h l] ]] H.
  rewrite mflhxu_utoZ /= /mflhxu_op /= utoZ_def /=.
  rewrite utoZ_def in H.
  rewrite [\B^1]lock /= -lock in H.
  rewrite 2!(@u2Z_zext 24 acx_size) Z2uK //=.
  have H1 : u2Z h * \B^1 + u2Z a * \B^2 < \B^1 * Zpos p by move: (min_u2Z l) => ?; omega.
  apply/(@ltZ_pmul2r \B^1) => //.
  rewrite 2!addZ0.
  rewrite (_ : (_ + _) * \B^1 = u2Z h * \B^1 + u2Z a * \B^2); last by rewrite (Zbeta_S 1); ring.
  by rewrite (mulZC (Zpos p)).
- (* if K < 0, we have a contradiction *) move=> H.
  move: (utoZ_pos mu) => H'.
  have ? : \B^1 * Zneg p < 0 by apply Zlt_neg_0.
  have ? : utoZ mu < 0 by omega.
  omega.
Qed.

(** msubu *)
Definition msubu_op (p : int (2 * 32)) (s : t) : t :=
match s with (lst, mu) =>
  let acx_reg := acx s in
  let hi_reg := hi s in
  let lo_reg := lo s in
    let sum := (hi_reg `|| lo_reg) in
      let new_sum := sum `- p in
        let lo_reg' := new_sum `% 32 in
      	  let sum' := shr_shrink 32 new_sum in
      	    let hi_reg' := sum' `% 32 in
      	      (lst, (acx_reg, (hi_reg', lo_reg'))) end.

Lemma msubu_utoZ : forall m a, utoZ m < \B^2 -> utoZ m >= u2Z a ->
  utoZ (msubu_op a m) = utoZ m - u2Z a.
Proof.
move=> [s [accu [ h l]]] a H H0.
rewrite /msubu_op /= utoZ_def /= utoZ_def /=.
have H1 : u2Z accu = 0.
  apply utoZ_acx_beta2 in H.
  rewrite /= in H.
  by rewrite H Z2uK.
rewrite H1 /= addZ0 u2Z_rem //.
rewrite u2Z_rem //.
rewrite Zbeta1E mulZBl.
rewrite (shr_shrink_overflow (shr_shrink 32 ((h `|| l) `- a))) //.
rewrite Z2uK; last by [].
rewrite subZ0 u2Z_sub.
- rewrite (u2Z_concat h l).
  by ring_simplify.
- rewrite (u2Z_concat h l) addZC.
  by rewrite utoZ_def /= H1 /= addZ0 in H0.
Qed.

Lemma msubu_utoZ_overflow : forall m a, utoZ m < \B^2 -> utoZ m < u2Z a ->
  utoZ (msubu_op a m) = \B^2 + utoZ m - u2Z a.
Proof.
move=> [s [accu [h l] ]] a H H0.
rewrite /msubu_op utoZ_def.
simpl lo. simpl hi. simpl acx.
have H1 : u2Z accu = 0.
  apply utoZ_acx_beta2 in H.
  rewrite /= in H.
  by rewrite H Z2uK.
rewrite H1 mul0Z addZ0 u2Z_rem // u2Z_rem // Zbeta1E mulZDl.
rewrite (shr_shrink_overflow (shr_shrink 32 ((h `|| l) `- a))); last by auto.
rewrite Z2uK; last by [].
rewrite mul0Z addZ0 u2Z_sub_overflow.
- rewrite (u2Z_concat h l) -Zbeta2E utoZ_def.
  simpl lo. simpl hi. simpl acx.
  rewrite H1 mul0Z.
  by ring_simplify.
- rewrite (u2Z_concat h l) addZC.
  by rewrite utoZ_def /= H1 /= addZ0 in H0.
Qed.

Lemma get_multu_op x z st : store.get x (store.multu_op z st) = store.get x st.
Proof. case: st => [st m0]. by rewrite /store.get /store.multu_op. Qed.

Lemma get_mflhxu_op : forall x st, store.get x (store.mflhxu_op st) = store.get x st.
Proof. move=> x [st m0]. by rewrite /store.get /store.mflhxu_op. Qed.

Lemma get_maddu_op : forall x z st, store.get x (store.maddu_op z st) = store.get x st.
Proof. move=> x z [st m0]. by rewrite /store.get /store.maddu_op. Qed.

Lemma get_msubu_op : forall x z st, store.get x (store.msubu_op z st) = store.get x st.
Proof. move=> x z [st m0]. by rewrite /store.get /store.msubu_op. Qed.

Lemma get_mthi_op : forall x z st, store.get x (store.mthi_op z st) = store.get x st.
Proof. move=> x0 z0 [st [a [hi0 lo0]]]. by rewrite /store.get /store.mthi_op. Qed.

Lemma get_mtlo_op : forall x z st, store.get x (store.mtlo_op z st) = store.get x st.
Proof. move=> x0 z0 [st [a [hi0 lo0]]]. by rewrite /store.get /store.mtlo_op. Qed.

End store.

(** Properties derived from the module store *)
Lemma utoZ_maddu_op k (m : store.t) (p : int (2 * 32)) :
  (k <= 64)%nat  ->  store.utoZ m < 2 ^^ k  ->  u2Z p < 2 ^^ k ->
  store.utoZ (store.maddu_op p m) < 2 ^^ (S k).
Proof.
move=> Hk Hm Hp.
rewrite store.utoZ_maddu.
- rewrite ZpowerS; omega.
- apply (@ltZ_leZ_trans (\B^2 * 1)) => //.
  rewrite mulZ1.
  apply (@ltZ_leZ_trans (2 ^^ k)) => //.
  apply/leZP; by rewrite Zbeta2E Zpower_2_le.
Qed.

Lemma lo_remainder_zero (s : store.t) :
  (exists K, store.utoZ s = K * \B^1) -> store.lo s = zero32.
Proof.
move=> [K H0].
have HK : 0 <= K.
  move: (store.utoZ_pos s).
  rewrite H0.
  case/Zle_0_mult_inv => H1; first omega.
  move: (Zbeta_gt0 1) => ?; omega.
rewrite store.utoZ_def in H0.
have {}H0 : (u2Z (store.hi s)  + u2Z (store.acx s) * \B^1) * \B^1 +
    u2Z (store.lo s) = K * \B^1 + 0.
  rewrite -H0 (Zbeta_S 1); ring.
apply poly_eq_inv in H0.
- apply u2Z_inj.
  rewrite /zero32 Z2uK //; tauto.
- split.
  + apply addZ_ge0; first exact: min_u2Z.
    apply mulZ_ge0 => //; exact/min_u2Z.
  + split => //.
    split; by [apply min_u2Z | apply max_u2Z].
Qed.

Module expr_m.

(** The language for expressions used in separating connectives. In this language,
variables are registers and constants are (32-bit) words. *)
Inductive expr : Type :=
| var_e : reg -> expr
| int_e : int 32 -> expr
| add_e : expr -> expr -> expr
| shl2_e : expr -> expr.

Notation "a '\+' b" := (add_e a b) (at level 61, left associativity) : mips_expr_scope.
Delimit Scope mips_expr_scope with mips_expr.
Local Open Scope mips_expr_scope.

Fixpoint vars (e : expr) : list reg :=
  match e with
    | var_e x => x :: nil
    | int_e _ => nil
    | e1 \+ e2 => vars e1 ++ vars e2
    | shl2_e e' => vars e'
  end.

(* TODO: useful? *)
Definition sext_16_32 (a : int 16) : int 32 := sext 16 a.

Lemma sext_16_32': forall n, n < 2 ^^ 15 -> sext_16_32 (Z2u 16 n) = Z2u 32 n.
Proof. move=> n Hn; by rewrite /sext_16_32 sext_Z2u. Qed.

Definition shl2 l (a : int l) := a `<< 2.
Arguments shl2 [l].

Lemma shift_2_mult_4 : forall (v : int 32) z, u2Z v = 4 * z -> v = shl2 (Z2u 32 z).
Proof.
move=> v [|p|p] H.
- apply u2Z_inj.
  by rewrite (@u2Z_shl _ _ _ 30) // Z2uK.
- apply u2Z_inj.
  have Hp : Zpos p < 2 ^^ 30.
    by apply Zpower_shift_2; rewrite -H /Zbeta; apply max_u2Z.
  have Hp' : 0 <= Zpos p < 2 ^^ 32.
    by split=> //; apply (@ltZ_trans (2 ^^ 30)).
  by rewrite (@u2Z_shl _ _ _ 30) // Z2uK // [_ ^^ _]/= mulZC.
- have : u2Z v < 0 by rewrite H.
  by move/Zlt_not_le: (min_u2Z v).
Qed.

Lemma shl_S : forall n, 0 <= n -> n + 1 < 2 ^^ 30 ->
  shl2 (Z2u 32 (n + 1)) = four32 `+ shl2 (Z2u 32 n).
Proof.
move=> [|p|p] Hn H.
- apply u2Z_inj.
  by rewrite u2Z_add // !(@u2Z_shl _ _ _ 30) // !Z2uK.
- have Hp : Zpos p < 2 ^^ 30.
    apply (@ltZ_trans (Zpos p + 1)) => //; omega.
  have Hp' : Zpos p < 2 ^^ 32 by apply (@ltZ_trans (2 ^^ 30)).
  apply u2Z_inj.
  rewrite u2Z_add //.
  + have Hp1 : 0 <= Zpos p + 1 < 2 ^^ 32.
      by split => //; apply (@ltZ_trans (2 ^^ 30)).
    rewrite !(@u2Z_shl _ _ _ 30) // !Z2uK //.
    by ring_simplify.
  + rewrite (@u2Z_shl _ _ _ 30) // !Z2uK // [_ ^^ _]/=.
    apply (@ltZ_leZ_trans (4 * 2 ^^ 30)) => //; omega.
- by move/Zlt_not_le: (Zlt_neg_0 p).
Qed.

(** Given an expression %\coqdocvar{e}%#e# and a store %\coqdocvar{s}%#s#, the function
   %\coqdocvar{eval}%#eval# returns the value of the expression %\coqdocvar{e}%#e# in store
   %\coqdocvar{s}%#s#: *)
Fixpoint eval e (s : store.t) :=
match e with
  | var_e w => store.get w s
  | int_e x => x
  | e1 \+ e2 => eval e1 s `+ eval e2 s
  | shl2_e e => eval e s `<< 2
end.

Notation "'[' x ']_' s" := (store.get x s) (at level 9, format "'[' [  x  ]_ s ']'") : mips_expr_scope.
Notation "'[' e ']e_' s" := (eval e s) (at level 9, format "'[' [  e  ]e_ s ']'") : mips_expr_scope.

Definition constant_expr (e : expr) := if vars e is nil then true else false.

Lemma constant_expr_add_e e1 e2 : constant_expr e1 -> constant_expr e2 ->
  constant_expr (e1 \+ e2).
Proof. rewrite /constant_expr /=. by destruct (vars e1). Qed.

Lemma constant_expr_add_e_inv e1 e2 : constant_expr (e1 \+ e2) ->
  constant_expr e1 /\ constant_expr e2.
Proof. rewrite /constant_expr /=; by destruct (vars e1). Qed.

Lemma constant_expr_shl2_e_inv : forall e, constant_expr (shl2_e e) ->
  constant_expr e.
Proof. by case. Qed.

Lemma constant_expr_prop : forall e, constant_expr e ->
  forall s s', [ e ]e_ s = [ e ]e_ s'.
Proof.
elim => //.
move=> e1 IH1 e2 IH2 H s s' /=.
case/constant_expr_add_e_inv : H => H1 H2.
by rewrite (IH1 H1 _ s') (IH2 H2 _ s').
move=> e IH /=.
move/constant_expr_shl2_e_inv.
move/IH => H s s'.
by rewrite (H _ s').
Qed.

Lemma eval_upd' : forall e x, ~ List.In x (vars e) ->
  forall s m v, [ e ]e_ (store.upd' x v s, m) = [ e ]e_ (s, m).
Proof.
elim => //.
- move=> g x /= g_x s m v.
  rewrite store.get_upd_p //; tauto.
- move=> e1 IHe1 e2 IHe2 x /= HnotIn s m v.
  rewrite IHe1; last by contradict HnotIn; apply List.in_or_app; left.
  rewrite IHe2 //; by contradict HnotIn; apply List.in_or_app; right.
- move=> e IH x /= HnotIn s m v; by rewrite IH.
Qed.

Lemma eval_upd e x : ~ List.In x (vars e) ->
  forall s v, [ e ]e_ (store.upd x v s) = [ e ]e_ s.
Proof.
move=> H [s m] v /=.
case: ifP => //=.
by rewrite eval_upd'.
Qed.

Lemma eval_inde_multiplier : forall e s m m', [ e ]e_ (s, m) = [ e ]e_ (s, m').
Proof.
elim=> //.
- move=> e1 H1 e2 H2 s m m' /=; f_equal; by [apply H1 | apply H2].
- move=> e IH s m m' /=; f_equal; by apply IH.
Qed.

(* TODO: generalize with substitution like in seplog? *)
Lemma eval_var_upd : forall x v s, x <> r0 ->
  [ var_e x ]e_(store.upd x v s) = v.
Proof. move=> x0 v s H. by rewrite /= store.get_upd'. Qed.

(** Control-flow commands are parameterized by a type for boolean tests: *)
Inductive expr_b : Type :=
| beq : reg -> reg -> expr_b
| bne : reg -> reg -> expr_b
| bltz : reg -> expr_b
| bgez : reg -> expr_b
| blez : reg -> expr_b
| bgtz : reg -> expr_b.

Definition vars_b (e : expr_b) : list reg :=
  match e with
    | beq r1 r2 => add_set r1 (r2 :: nil)
    | bne r1 r2 => add_set r1 (r2 :: nil)
    | bltz r => r :: nil
    | bgez r => r :: nil
    | blez r => r :: nil
    | bgtz r => r :: nil
  end.

Definition neg t :=
match t with
  | beq r1 r2 => bne r1 r2
  | bne r1 r2 => beq r1 r2
  | bltz r => bgez r
  | bgez r => bltz r
  | blez r => bgtz r
  | bgtz r => blez r
end.

Definition eval_b (t : expr_b) (s : store.t) : bool :=
match t with
  | beq r1 r2 => u2Z (store.get r1 s) == u2Z (store.get r2 s)
  | bne r1 r2 => negb (u2Z (store.get r1 s) == u2Z (store.get r2 s))
  | bltz r => Zlt_bool (s2Z (store.get r s)) 0
  | bgez r => Zle_bool 0 (s2Z (store.get r s))
  | blez r => Zle_bool (s2Z (store.get r s)) 0
  | bgtz r => Zlt_bool 0 (s2Z (store.get r s))
end.

Lemma eval_b_neg : forall t s, eval_b (neg t) s = ~~ eval_b t s.
Proof.
case => //=.
move=> r r' s; by rewrite negbK.
move=> r s; by rewrite Z.leb_antisym.
move=> r s; rewrite Z.leb_antisym; by apply negbRL.
move=> r s; by rewrite Z.leb_antisym negbK.
by move=> r s; rewrite Z.leb_antisym.
Qed.

End expr_m.

(** * Assertion language *)

Require Import finmap. (* NB: is here on purpose, put earlier it will cause conflicts with the :: notation *)

(* TODO: move *)
Module Int32 <: finmap.EQTYPE.
  Definition A : eqType := int_eqType 32.
End Int32.

Module heap := finmap.map order.NatOrder Int32.
Module heap_tac_m := finmap.Map_Tac heap.

Notation "k '#' m" := (heap.disj k m) : heap_scope.
Notation "k '\U' m" := (heap.union k m) : heap_scope.
Notation "k '\D\' m" := (heap.difs k m) : heap_scope.
Notation "k '\d\' m" := (heap.dif k m) : heap_scope.
Local Open Scope heap_scope.

Module assert_m.

(** Assertions are encoded as truth-functions from states to
%\coqdocvar{Prop}%#Prop#, the type of predicates in Coq (this technique
is called %\textsl{shallow embedding}%#shallow embedding#). Using this type,
one can easily encode any first-order predicate. *)
Definition assert := store.t -> heap.t -> Prop.

Definition FF : assert := while.FF store.t heap.t.
Definition TT : assert := while.TT store.t heap.t.
Definition Not (P : assert) : assert := while.Not P.
Notation "P '//\\' Q" := (while.And store.t heap.t P Q) (at level 80, right associativity) : mips_assert_scope.
Notation "P '\\//' Q" := (while.Or store.t heap.t P Q) (at level 80, right associativity) : mips_assert_scope.
Notation "P ===> Q" := (while.entails store.t heap.t P Q) (at level 90, no associativity) : mips_assert_scope.
Notation "P <==> Q" := (while.equiv store.t heap.t P Q) (at level 90, no associativity) : mips_assert_scope.
Delimit Scope mips_assert_scope with mips_assert.
Local Open Scope mips_assert_scope.

(* The predicate that is true when variables #\coqdocvar{x}# and
%\coqdocvar{y}%#y# have the same contents is encoded as follows: *)

Import expr_m.
Local Open Scope mips_expr_scope.
Definition x_EQ_y (x y : reg) : assert := fun s _ => [ x ]_ s = [ y ]_ s .

Local Open Scope heap_scope.

(** The %\textsl{separating conjunction}%#separating conjunction# %\ensuremath{P \star Q}%#P ** Q#
holds in a state whose heap can be divided into two disj heaps such that
$P$#P# and $Q$#Q# hold: *)
Definition con (P Q : assert) : assert := fun s h =>
  exists h1 h2, h1 # h2 /\ h = h1 \U h2 /\ P s h1 /\ Q s h2.
Notation "P ** Q" := (con P Q) (at level 80, right associativity) : mips_assert_scope.

Lemma con_cons (P Q : assert) s h1 h2 :
  h1 # h2 -> P s h1 -> Q s h2 -> (P ** Q) s (h1 \U h2).
Proof. move=> ? ? ?; by exists h1, h2. Qed.

Lemma semi_distributivity (P1 P2 Q : assert) : (P1 //\\ P2) ** Q ===> (P1 ** Q) //\\ (P2 ** Q).
Proof. move=> ? ? [h1 [h2 [? [? [[? ?] ?]]]]]; split; exists h1; exists h2 => //. Qed.

(** Extensionality of predicates can be safely added to Coq (see Coq FAQ) *)
Axiom assert_ext : forall P Q, (P <==> Q) -> P = Q.

Lemma AndCE P Q : (P //\\ Q) = (Q //\\ P).
Proof. apply assert_ext=> s h; split; case=> HP HQ //. Qed.

Lemma conC P Q : P ** Q ===> Q ** P.
Proof.
move=> s h [h1 [h2 [Ha [Hb [Hc Hd]]]]].
exists h2, h1.
split; first by apply heap.disj_sym.
split => //.
apply trans_eq with (h1 \U h2) => //.
by apply heap.unionC.
Qed.

Lemma conCE P Q : (P ** Q) = (Q ** P).
Proof. apply assert_ext => s h; split => H; by apply conC. Qed.

Module map_tac_m := finmap.Map_Tac heap.

Lemma conA P Q R : (P ** Q) ** R ===> P ** (Q ** R).
Proof.
move=> s h [h12 [h3 [H1 [H2 [H3 H4]]]]].
case: H3 => [h1 [h2 [H5 [H6 [H7 H8]]]]].
exists h1, (h2 \U h3).
split.
- apply heap.disjhU => //.
  by map_tac_m.Disj.
- split.
  + by rewrite heap.unionA H2 H6.
  + split => //.
    exists h2, h3.
    split => //.
    by map_tac_m.Disj.
Qed.

Lemma conAE P Q R : ((Q ** P) ** R) = (Q ** (P ** R)).
Proof.
apply assert_ext=> s h.
split; case=> h1 [h2 [H1 [H2 [H3 H4]]]].
- case: H3 => h11 [h12 [H31 [ H32 [ H33 H34]]]].
  exists h11, (h12 \U h2).
  repeat (split => // || map_tac_m.Disj || map_tac_m.Equal).
  exists h12, h2.
  repeat (split => // || map_tac_m.Disj || map_tac_m.Equal).
- case: H4 => h21 [h22 [H41 [H42 [H43 H44]]]].
  exists (h1 \U h21), h22.
  repeat (split => // || map_tac_m.Disj || map_tac_m.Equal).
  exists h1, h21.
  repeat (split => // || map_tac_m.Disj || map_tac_m.Equal).
Qed.

Lemma con_TT P : P ===> P ** TT.
Proof.
move=> s h.
exists h, heap.emp; split.
by apply heap.disjhe.
by rewrite heap.unionhe.
Qed.

Lemma con_Q_con_TT P Q : P ** Q ===> P ** TT.
Proof.
move=> s h [h1 [h2 [H1 [H2 [H3 H4]]]]].
by exists h1, h2.
Qed.

Lemma exists_conC A_type P (Q : _) s h :
  (((fun s h => exists A : A_type, P A s h) ** Q) s h ->
  (fun s h => exists A, (P A ** Q) s h) s h).
Proof.
move=> /=.
case=> h1 [h2 [h1dh2 [h1Uh2 [[A Hh1] Hh2]]]].
by exists A, h1, h2.
Qed.

Lemma exists_conC' A_type P (Q : _) s h :
  ((fun s h => exists A, (P A ** Q) s h) s h ->
  ((fun s h => exists A : A_type, P A s h) ** Q) s h).
Proof.
move=> /=.
case=> A [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
exists h1, h2.
repeat (split => //).
by exists A.
Qed.

Lemma monotony (P1 P2 Q1 Q2 : assert) sm sm' h :
  (forall h', P1 sm h' -> P2 sm' h') ->
  (forall h', Q1 sm h' -> Q2 sm' h') ->
  (P1 ** Q1) sm h -> (P2 ** Q2) sm' h.
Proof.
move=> H1 H2 [h1 [h2 [H3 [H4 [H5 H6]]]]].
exists h1, h2; repeat (split; eauto).
Qed.

Definition emp : assert := fun s h => h = heap.emp.

Lemma con_emp P : P ** assert_m.emp ===> P.
Proof.
move=> s h [h1 [h2 [Hdisj [Hunion [HPh1 Hemph2]]]]].
rewrite /emp in Hemph2; subst h2.
by rewrite Hunion heap.unionhe.
Qed.

Lemma con_emp' P : P  ===> P ** assert_m.emp.
Proof.
move=> s h H.
exists h, heap.emp; repeat (split => //).
by apply heap.disjhe.
by rewrite heap.unionhe.
Qed.

Lemma con_emp_equiv P : (P ** assert_m.emp) = P.
Proof. apply assert_ext; split; [apply con_emp | apply con_emp']. Qed.

Definition imp (P Q : assert) : assert := fun s h =>
  forall h', h # h' /\ P s h' -> forall h'', h'' = h \U h' -> Q s h''.
Notation "P -* Q" := (imp P Q) (at level 80) : mips_assert_scope.

Lemma mp P Q : Q ** (Q -* P) ===> P.
Proof.
move=> s h [h1 [h2 [Hh1h2disj [Hh1h2union [HQh1 HQimpP]]]]].
apply HQimpP with h1.
split => //.
apply heap.disj_sym => //.
rewrite heap.unionC => //; by apply heap.disj_sym.
Qed.

Lemma pm P Q : Q ===> P -* (P ** Q).
Proof.
move=> s h HQ h' [Hhh'disj HPh'] h'' Hhh'union.
exists h', h; repeat (split => //).
apply heap.disj_sym => //.
rewrite heap.unionC => //; by apply heap.disj_sym.
Qed.

Lemma currying (P1 P2 P3 : assert) s :
  (forall h, (P1 ** P2) s h -> P3 s h) ->
  (forall h, P1 s h -> (P2 -* P3) s h).
Proof.
move=> H h H' h' [H1 H2] h'' H3.
apply H => //; by exists h, h'.
Qed.

Lemma uncurrying (P1 P2 P3 : assert) s :
  (forall h, P1 s h -> (P2 -* P3) s h) ->
  (forall h, (P1 ** P2) s h -> P3 s h).
Proof.
move=> H h [h1 [h2 [H1 [H2 [HP1h1 H4]]]]].
apply H in HP1h1; by eapply HP1h1; eauto.
Qed.

Definition strictly_exact (P : assert) := forall s h h', P s h /\ P s h' -> h = h'.

Lemma strictly_exact_con P Q : assert_m.strictly_exact P ->
  assert_m.strictly_exact Q -> assert_m.strictly_exact (P ** Q)%mips_assert.
Proof.
move=> HP HQ s h h' [].
case=> h1 [h2 [H1 [-> [H3 H4]]]].
case=> h1' [h2' [H1' [-> [H3' H4']]]].
by rewrite (HP s h1 h1') // (HQ s h2 h2').
Qed.

Lemma strictly_exact_prop P Q :
  strictly_exact Q -> P //\\ (Q ** TT) ===> Q ** (Q -* P).
Proof.
move=> HQ s h [H1 [h1 [h2 [H2 [H3 [H4 _]]]]]].
exists h1, h2; repeat (split => //).
move => h' [H'1 H'2] h'' H''.
suff : h'' = h by move=> ->.
by rewrite H'' H3 (HQ _ _ _ (conj H4 H'2)) // heap.unionC.
Qed.

Definition domain_exact (P : assert) :=
  forall s h h', P s h /\ P s h' -> heap.dom h = heap.dom h'.

Definition constant_assert (P : assert_m.assert) :=
  forall s s' h h', P s h -> P s' h' -> h = h'.

Lemma constant_assert_con P Q :
  constant_assert P -> constant_assert Q ->
  constant_assert (P ** Q)%mips_assert.
Proof.
move=> HP HQ.
rewrite /constant_assert => s s' h h'.
case=> h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case=> h'1 [h'2 [h'1_d_h'2 [h'1_U_h'2 [Hh'1 Hh'2]]]].
subst h h'.
by rewrite (HP _ _ _ _ Hh1 Hh'1) (HQ _ _ _ _ Hh2 Hh'2).
Qed.

Definition is_pure (P : assert) := forall s h h', P s h <-> P s h'.

Definition bang (e : store.t -> Prop) : assert := fun s h => e s /\ h = heap.emp.

Lemma store_upd_con P Q s h str val :
  ((fun s h => P (store.upd str val s) h) ** fun s h => Q (store.upd str val s) h) s h ->
  (P ** Q) (store.upd str val s) h.
Proof. case=> h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]; by exists h1, h2. Qed.

Notation "! e" := (bang e) (at level 4) : mips_assert_scope.

Lemma pure_upd (P : store.t -> Prop ) str val s h :
  (P s -> P (store.upd str val s)) -> !P s h -> !P  (store.upd str val s) h.
Proof. move=> H [] X1 X2; split => //. by apply H. Qed.

Lemma bangify (P P' : store.t -> Prop) s h : (P s -> P' s) -> !P s h -> !P' s h.
Proof.  move=> H [] H1 H2. rewrite /bang. by auto. Qed.

Lemma con_and_bang_R (P : assert) (Q : store.t -> Prop) s h :
  P s h -> Q s -> (P ** !Q) s h.
Proof.
move=> HP HQ.
exists h, heap.emp.
split; first by apply heap.disjhe.
split => //; by rewrite heap.unionhe.
Qed.

Lemma con_and_bang_L (P : assert) (Q : store.t -> Prop) s h :
  P s h -> Q s -> (!Q ** P) s h.
Proof.
rewrite assert_m.conCE.
by apply con_and_bang_R.
Qed.

Lemma con_and_bang_inv_R (P : assert) (Q : store.t -> Prop) s h : (P ** !Q) s h -> P s h /\ Q s.
Proof.
case=> h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh2 => ? Hh2; subst h2.
rewrite heap.unionhe in h1_U_h2; by subst h1.
Qed.

Lemma con_and_bang_inv_L (Q : assert) (P : store.t -> Prop) s h : (!P ** Q) s h -> P s /\ Q s h.
Proof.
case=> h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh1 => ? Hh1; subst h1.
rewrite heap.unioneh in h1_U_h2; by subst h2.
Qed.

Lemma con_bang_L (P Q : store.t -> Prop) s h : (!P ** !Q) s h -> !P s h.
Proof.
case=> h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh1 => ? Hh1; subst h1.
case: Hh2 => ? Hh2; subst h2.
subst h.
by rewrite heap.unioneh.
Qed.

Lemma con_bang_L_pull_out (P : store.t -> Prop) (Q1 Q2 : assert) s h :
  (P s -> Q1 s h -> Q2 s h) ->
  ((!P ** Q1) s h -> (!P ** Q2) s h).
Proof.
move=> H [h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]]].
exists heap.emp, h2.
split; first by apply heap.disjeh.
case: Hh1 => ? Hh1; subst h1.
split; first by assumption.
split; first by done.
rewrite heap.unioneh in h1_U_h2.
subst h2.
by apply H.
Qed.

Lemma con_bangE_R P Q : (fun s h => P s /\ Q s h) = (!P ** Q).
Proof.
apply assert_ext; split.
  case=> HP HQ.
  exists heap.emp, h.
  split; first by apply heap.disjeh.
  split; first by rewrite heap.unioneh.
  done.
move=> H.
by apply con_and_bang_inv_L in H.
Qed.

Lemma con_bangE_L P Q : (fun s h => P s h /\ Q s) = (P ** !Q).
Proof.
rewrite conCE.
rewrite -con_bangE_R.
apply assert_m.assert_ext; split => ?; tauto.
Qed.

Lemma con_bangE (P Q : store.t -> Prop) : (!P ** !Q) = (!(fun s => P s /\ Q s)).
Proof.
apply assert_ext => s h; split => H.
case: H => h1 [h2 [h1_d_h2 [h1_U_h2 [[h1e Hh1] [h2e Hh2]]]]].
subst.
rewrite /bang.
by rewrite heap.unioneh.
exists heap.emp, heap.emp.
split.
by apply heap.disjeh.
split.
  rewrite heap.unioneh.
  by case: H => _ ->.
unfold bang in *.
tauto.
Qed.

(** The %\textsl{mapsto}%#mapsto# connective %\coqdocvar{e1}\ensuremath{\mapsto}\coqdocvar{e2}%#e1 |~> e2# holds in a state with a store %\coqdocvar{s}%#s# and a
singleton heap with address %\coqdocvar{eval e1 s}%#eval e1 s# and
contents %\coqdocvar{eval e2 s}%#eval e2 s#, under the restriction that
the heap-location is word-aligned: *)
Definition mapsto e e' : assert := fun s h =>
  exists p, u2Z ([ e ]e_ s) = 4 * Z_of_nat p /\ h = heap.sing p ([ e' ]e_ s).
Notation "e1 |~> e2" := (mapsto e1 e2) (at level 77) : mips_assert_scope.

Lemma singl_equal s h1 h2 e1 e2 e3 e4 :
  (e1 |~> e2) s h1 -> (e3 |~> e4) s h2 ->
  [ e1 ]e_ s = [ e3 ]e_ s -> [ e2 ]e_ s = [ e4 ]e_ s -> h1 = h2.
Proof.
move=> [p [H1 ->]] [p' [H3 ->]] Heq1 ->; f_equal.
rewrite Heq1 in H1; omega.
Qed.

Lemma strictly_exact_mapsto e e' : assert_m.strictly_exact (e |~> e').
Proof.
rewrite /assert_m.strictly_exact => s h h' [Hh Hh'].
eapply assert_m.singl_equal.
by apply Hh.
by apply Hh'.
done.
done.
Qed.

Lemma mapsto_con_get st h e1 e2 P : (e1 |~> e2 ** P) st h ->
  heap.get '| u2Z ([ e1 ]e_ st) / 4 | h = Some ([ e2 ]e_ st).
Proof.
move=> [h1 [h2 [h1dh2 [-> [[p [Hh1 Hh1']] _]]]]]; apply heap.get_union_L => //.
by rewrite Hh1' Hh1 mulZC Z_div_mult // Zabs2Nat.id heap.get_sing.
Qed.

Lemma mapsto_inv_addr e e' st h : (e |~> e') st h ->
  u2Z ([ e ]e_ st) mod 4 = 0.
Proof. move=> [e4 [-> _]]; by rewrite mulZC Z_mod_mult. Qed.

Lemma mapsto_inj e a b st h : (e |~> a) st h -> (e |~> b) st h ->
  [ a ]e_ st  = [ b ]e_ st.
Proof.
move=> [pa [Hpa1 Hpa2]] [pb [Hpb1 Hpb2]].
have : pa = pb by omega.
move=> ?; subst pb.
rewrite Hpa2 in Hpb2.
by move/heap.sing_inj : Hpb2.
Qed.

Lemma mapsto_con_inj e a b P Q st h :
  (e |~> a ** P) st h -> (e |~> b ** Q) st h -> [ a ]e_ st = [ b ]e_ st.
Proof.
move/mapsto_con_get=> Ha; move/mapsto_con_get=> Hb.
rewrite Ha in Hb; by case: Hb.
Qed.

Lemma mapsto_ext e1 e2 sm' e3 e4 sm h :
  [ e1 ]e_ sm' = [ e3 ]e_ sm -> [ e2 ]e_ sm' = [ e4 ]e_ sm ->
  (e1 |~> e2) sm' h -> (e3 |~> e4) sm h.
Proof.
move=> H1 H2 [p [Hp Hh]].
exists p; split; by rewrite -?H1 -?H2.
Qed.

Lemma constant_assert_mapsto e1 e2 :
  constant_expr e1 -> constant_expr e2 ->
  constant_assert (e1 |~> e2)%mips_assert.
Proof.
move=> He1 He2.
rewrite /constant_assert.
move=> s s' h h'.
case=> x [Hx ->] [y [Hy ->]].
rewrite (constant_expr_prop _ He1 s s') in Hx.
have ? : x = y by omega. subst y.
by rewrite (constant_expr_prop _ He2 s s').
Qed.

(** Using the separating conjunction, the mapsto connective can be generalized
to arrays of words: %\ensuremath{e \Mapsto a::b::...}%#e |--> a::b::...# holds in a state whose heap
contains a list of contiguous words %\ensuremath{a, b,} etc.\ %#a, b, etc.# starting at address
%\coqdocvar{eval e s}%#eval e s#: *)
Fixpoint mapstos e l : assert :=
match l with
  | nil => fun s h => u2Z ([ e ]e_ s) mod 4 = 0 /\ emp s h
  | hd :: tl => (e |~> int_e hd) ** (mapstos (e \+ int_e four32) tl)
end.
Notation "x '|-->' l" := (mapstos x l) (at level 77) : mips_assert_scope.

Module map_prop_m := finmap.Map_Prop heap.

Lemma strictly_exact_mapstos : forall e' e, assert_m.strictly_exact (e |--> e')%mips_assert.
Proof.
elim.
- by move=> e /= s h h' [] [] _ -> [] _ ->.
- move=> h t IH e /=.
  apply strictly_exact_con.
  by apply strictly_exact_mapsto.
  by apply IH.
Qed.

Lemma mapstos_inv_emp : forall l e st, (e |--> l) st heap.emp -> l = nil.
Proof.
elim=> // hd tl IH e st /= [h1 [h2 [Hdisj [Hunion [Hh1 Hh2]]]]].
case/heap.union_emp_inv : Hunion => H1 H2; subst h1 h2.
case: Hh1 => p [Hp].
by case/map_prop_m.emp_sing_dis.
Qed.

Lemma mapstos_inv_addr : forall l e st h, (e |--> l) st h -> u2Z ([ e ]e_ st) mod 4 = 0.
Proof.
case.
- rewrite /= => e st h [H1 H2].
  rewrite /emp in H2; by subst h.
- move => hd tl e st h /= [h1 [h2 [Hdisj [Hunion [[p [Hp1 Hp2]] Hh2]]]]].
  by rewrite Hp1 mulZC Z_mod_mult.
Qed.

Lemma mapsto1_mapstos e1 e2 : (e1 |~> int_e e2) = (e1 |--> e2 :: nil).
Proof.
apply assert_m.assert_ext; split.
case=> p [H1 H2] /=.
exists h; exists heap.emp.
split; first by apply heap.disjhe.
split; first by rewrite heap.unionhe.
split; first by exists p.
split; last by done.
rewrite u2Z_add_mod //.
by rewrite H1 mulZC Z_mod_mult.
case=> h1 [h2 [h1dh2 [h1Uh2 [Hh1 [Hh2 Hh2']]]]].
by rewrite h1Uh2 Hh2' heap.unionhe.
Qed.

Lemma mapsto2_mapstos e1 e2 e3 :
  (e1 |~> int_e e2 ** e1 \+ int_e four32 |~> int_e e3) = (e1 |--> e2 :: e3 :: nil).
Proof.
apply assert_m.assert_ext; split.
rewrite [List.cons e3 _]lock /= -lock.
apply assert_m.monotony => // h'.
by rewrite mapsto1_mapstos.
rewrite [List.cons e3 _]lock /= -lock.
apply assert_m.monotony => // h'.
by rewrite mapsto1_mapstos.
Qed.

Lemma mapstos_inv_dom : forall L e st h, u2Z ([ e ]e_st) + 4 * Z<=nat (size L) < \B^1 ->
  (e |--> L) st h ->
  iota '|u2Z ([ e ]e_ st) / 4| (size L) = heap.dom h.
Proof.
elim.
- move=> e st h /= _ [Hheap1 Hheap2].
  rewrite /assert_m.emp in Hheap2.
  by rewrite Hheap2 heap.dom_emp.
- move=> hd tl IH s st h Hfit /= [h1 [h2 [Hdisj [Hunion [[p [Hp Hh1]] Hh2]]]]].
  rewrite [size _]/= Z_S in Hfit.
  rewrite Hunion Hh1 heap.dom_union_sing /=.
  + rewrite Hp mulZC Z_div_mult_full // Zabs2Nat.id; f_equal.
    have -> : S p = '|u2Z ([ s \+ int_e four32 ]e_ st) / 4|.
      have -> : p = '|u2Z ([ s ]e_ st)%mips_expr / 4|.
        by rewrite Hp mulZC Z_div_mult_full // Zabs2Nat.id.
      rewrite /= u2Z_add_Z2u //.
      * rewrite {2}(_ : 4 = 1 * 4) // Z_div_plus_full // S_Zabs_nat //.
        apply Z_div_pos => //.
        by apply min_u2Z.
      * rewrite -Zbeta1E; omega.
    apply IH => //.
    rewrite [u2Z _]/= u2Z_add_Z2u //.
    * omega.
    * rewrite -Zbeta1E; omega.
  + apply order.lt_lb => m Hm.
    have : u2Z ([ s \+ int_e four32 ]e_ st) + 4 * Z_of_nat (size tl) < \B^1.
      rewrite [eval _ _]/= u2Z_add_Z2u // -?Zbeta1E; omega.
    move/(IH _ _ h2) => /(_ Hh2).
    rewrite [ [ _ ]e_ _ ]/= u2Z_add_Z2u // -?Zbeta1E Hp; last omega.
    rewrite {2}(_ : 4 = 1 * 4) // Z_div_plus_full // mulZC Z_div_mult_full //.
    move=> X; rewrite -X in Hm; move: Hm.
    rewrite mem_iota => /andP[Hm1 Hm2].
    rewrite /heap.ltl /order.NatOrder.ltA.
    rewrite Zabs_nat_Zplus // in Hm1; last exact/Zle_0_nat.
    rewrite Zabs2Nat.id (_ : '|1| = 1%nat) // in Hm1; rewrite /ltn /=; ssromega.
Qed.

Lemma mapstos_inv_cdom : forall lst e s h,
  u2Z ([ e ]e_ s) + 4 * Z_of_nat (size lst) < \B^1 ->
  (e |--> lst) s h ->
  heap.cdom h = List.map (fun e => [ int_e e ]e_s) lst.
Proof.
elim.
  rewrite /= => e s h _ [H1 H2].
  by rewrite H2 heap.cdom_emp.
move=> hd tl IH e s h H /=.
case=> h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh1 => p [Hp Hh1].
rewrite h1_U_h2 Hh1.
have IH' : u2Z [e \+ int_e four32 ]e_ s + 4 * Z_of_nat (size tl) < \B^1.
  rewrite [size _]/= Z_S in H.
  rewrite [Z<=u _]/= u2Z_add_Z2u //; first omega.
  rewrite -Zbeta1E; omega.
move/assert_m.mapstos_inv_dom : (Hh2).
move/(_ IH') => Hh2'.
apply IH in Hh2; last by [].
rewrite heap.cdom_union.
by rewrite heap.cdom_sing /= Hh2.
move=> i j.
rewrite heap.dom_sing.
rewrite seq.inE.
move/eqP => ?; subst p.
rewrite -Hh2'.
rewrite mem_iota => /andP[Hj _].
rewrite /heap.ltl /order.NatOrder.ltA.
apply/ltP.
rewrite /= in Hj.
rewrite u2Z_add_Z2u // in Hj; last first.
  rewrite [size _]/= Z_S in H.
  rewrite -Zbeta1E; omega.
rewrite Hp mulZC Z_div_plus_full_l // Z_div_same_full // in Hj.
rewrite Zabs_nat_Zplus // in Hj; last by apply Zle_0_nat.
rewrite Zabs2Nat.id (_ : '|1| = 1%nat) // in Hj.
ssromega.
Qed.

Lemma mapstos_inv : forall lst e s h,
  u2Z ([ e ]e_s)%mips_expr + 4 * Z_of_nat (length lst) < \B^1 ->
  (e |--> lst)%mips_assert s h ->
  heap.dom h = List.seq '|u2Z ([ e ]e_ s) / 4| (length lst) /\
  heap.cdom h = List.map (fun e => [ int_e e ]e_s)%mips_expr lst.
Proof.
intros.
split.
symmetry.
by apply assert_m.mapstos_inv_dom.
by eapply mapstos_inv_cdom; eauto.
Qed.

Lemma mapstos_inc_inv st h e l : u2Z ([ e ]e_ st) + 4 * Z_of_nat (size l) < \B^1 ->
  (e |--> l ** assert_m.TT) st h ->
    inc (iota '|u2Z ([ e ]e_ st) / 4| (size l)) (heap.dom h).
Proof.
move=> Hfit [h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]]].
apply/incP => x /inP Hx.
apply mapstos_inv_dom in Hh1.
- rewrite Hh1 in Hx.
  rewrite h1Uh2.
  apply/inP.
  by apply heap.in_dom_union_L.
- exact Hfit.
Qed.

Lemma mapstos_get_inv : forall n l e s h, length l = n ->
  u2Z (eval e s) + 4 * Z_of_nat n < \B^1 ->
  (e |--> l) s h ->
  forall i elt, (i < n)%nat ->
    onth i l = Some elt ->
    heap.get ('|u2Z ([ e ]e_ s) / 4| + i)%nat h = Some elt.
Proof.
elim.
- by case.
- move=> n IH [|hd tl] // x s h [len_l] Hfit mem [|i] elt.
  + move=> _ /= [?]; subst hd.
    case: mem => h1 [h2 [Hunion [Hdisj [Hh1 Hh2]]]].
    case: Hh1 => p [Hp Hh1].
    by rewrite addn0 Hdisj Hh1 Hp mulZC Z_div_mult_full // Zabs2Nat.id heap.get_union_sing_eq.
  + rewrite ltnS => /= Hi Helt.
    rewrite /= in mem.
    case: mem => h1 [h2 [Hdisj [Hunion [Hh1 Hh2]]]].
    have : u2Z ([ x \+ int_e four32 ]e_ s)%mips_expr + 4 * Z_of_nat n < \B^1.
      rewrite Z_S in Hfit.
      rewrite [u2Z _]/= u2Z_add_Z2u //.
      omega.
      rewrite -Zbeta1E; omega.
    move/(IH _ (x \+ int_e four32) s h2 len_l).
    move/(_ Hh2 _ _ Hi Helt).
    rewrite [u2Z _]/= u2Z_add_Z2u //; last first.
      rewrite Z_S in Hfit; rewrite -Zbeta1E; omega.
    rewrite -{1}(mul1Z 4) Z_div_plus_full // Zabs_nat_Zplus //; last first.
      apply Z_div_pos => //; exact/min_u2Z.
    rewrite -addnA => {}IH.
    rewrite Hunion; exact: heap.get_union_R.
Qed.

Lemma mapstos_inj : forall n l1 l2 e st h, size l1 = n -> size l2 = n ->
  (e |--> l1) st h -> (e |--> l2) st h -> l1 = l2.
Proof.
elim.
- case=> //; by case.
- move=> n IH [|hd1 tl1]// [|hd2 tl2]// e st h /= [H1] [H2]
    [h1 [h2 [Hdisj [Hunion [[p1 [Hh11 Hh12]] Hh2]]]]] [h1' [h2' [Hdisj' [Hunion' [[p1' [Hh11' Hh12']] Hh2']]]]].
  have : p1 = p1' by omega.
  move=> ?; subst p1'.
  rewrite Hunion' in Hunion.
  move: (heap.union_inv _ _ _ _ Hunion).
  rewrite {1}Hh12 {1}Hh12'.
  rewrite 2!heap.dom_sing.
  move/(_ (refl_equal _)).
  apply heap.disj_sym in Hdisj.
  apply heap.disj_sym in Hdisj'.
  case/(_ Hdisj' Hdisj)=> Hh1 X2; subst h1' h2'.
  rewrite (IH _ _ _ _ _ H1 H2 Hh2 Hh2').
  f_equal.
  rewrite Hh12 in Hh1.
  by move/heap.sing_inj : Hh1.
Qed.

Lemma mapstos_con_inj n l1 l2 e st h P Q :
  u2Z ([ e ]e_ st) + 4 * Z_of_nat n < \B^1 ->
  size l1 = n -> size l2 = n ->
  (e |--> l1 ** P) st h -> (e |--> l2 ** Q) st h ->
  l1 = l2.
Proof.
move=> e_fit len_l1 len_l2.
case=> h1 [h2 [h1dh2 [h1Uh2 [Hh1 Hh2]]]].
case=> h1' [h2' [h1'dh2' [h1'Uh2' [Hh1' Hh2']]]].
have ? : h1 = h1'.
  rewrite h1Uh2 in h1'Uh2'.
  have dom_h1_h1' : heap.dom h1 = heap.dom h1'.
    apply assert_m.mapstos_inv_dom in Hh1; last by rewrite len_l1.
    apply assert_m.mapstos_inv_dom in Hh1'; last by rewrite len_l2.
    by rewrite -Hh1 -Hh1' len_l1 len_l2.
  apply (heap.union_inv h1 h1' h2 h2' h1'Uh2') => //; by apply heap.disj_sym.
subst h1'.
by apply assert_m.mapstos_inj with n e st h1.
Qed.

Lemma mapstos_ext : forall e st l st' h e', [ e ]e_st = [ e' ]e_st' ->
  (e |--> l) st h -> (e' |--> l) st' h.
Proof.
move=> e st l; elim: l e st.
- by move=> ? ? ? ? ? /= ->.
- move=> hd tl IH e0 st st' h e' Heq /= [h1 [h2 [Hdisj [Hunion [Hh1 Hh2]]]]].
  exists h1, h2; do 2 (split; first by done); split.
  + by move: Hh1; apply mapsto_ext.
  + apply (IH (e0 \+ int_e four32) st) => //=; by rewrite Heq.
Qed.

Lemma mapsto_get1' s h e e1 P : (e |~> int_e e1 ** P) s h ->
  heap.get '|u2Z ([ e ]e_ s)/ 4| h = Some e1.
Proof.
case=> h1 [h2 [h1_d_h2 [h1_U_h2 [Hh1 Hh2]]]].
case: Hh1 => p [Hp Hh1].
rewrite h1_U_h2.
apply heap.get_union_L => //.
by rewrite Hh1 Hp mulZC Z_div_mult_full // Zabs2Nat.id heap.get_sing.
Qed.

Lemma mapstos_get1 s h e e1 e2 P : (e |--> e1 :: e2 :: nil ** P) s h ->
  heap.get '|u2Z ([ e ]e_ s)/ 4| h = Some e1.
Proof. rewrite assert_m.conAE; by move/mapsto_get1'. Qed.

Lemma mapstos_get2 s h e e1 e2 P : (e |--> e1 :: e2 :: nil ** P) s h ->
  heap.get '|u2Z ([ e ]e_ s `+ four32) / 4| h = Some e2.
Proof. rewrite assert_m.conAE assert_m.conCE !assert_m.conAE; by move/mapsto_get1'. Qed.

Lemma constant_assert_mapstos : forall l e, constant_expr e ->
  constant_assert (e |--> l).
Proof.
elim => [e | h t IH e He] /=.
- rewrite /constant_assert => He s s' h h'.
  by case=> _ -> [_ ->].
- apply constant_assert_con.
  + by apply constant_assert_mapsto.
  + by apply IH, constant_expr_add_e.
Qed.

Lemma constant_assert2_mapstos e l s s' h h' :
  u2Z [e ]e_ s + 4 * Z_of_nat (length l) < \B^1 ->
  u2Z [e ]e_ s' + 4 * Z_of_nat (length l) < \B^1 ->
  (e |--> l) s h -> (e |--> l) s' h' ->
  [ e ]e_ s = [ e ]e_ s' -> h = h'.
Proof.
move=> Hfit Hfit'.
move/(mapstos_inv _ _ _ _ Hfit) => [H1 H2].
move/(mapstos_inv _ _ _ _ Hfit') => [H'1 H'2].
move=> e_e'.
apply heap.dom_cdom_heap.
by rewrite H1 H'1 e_e'.
rewrite H2 H'2; by apply List.map_ext.
Qed.

(** inde l P  iff  the truth of assertion P does not depend on the value of registers in list l *)
Definition inde (l : list store.var) (P : assert) := forall s h,
  (forall x v, List.In x l -> (P s h <-> P (store.upd x v s) h)).

Lemma inde_nil : forall P, inde nil P. Proof. by []. Qed.

Lemma incl_inde : forall a b P, inde b P -> List.incl a b -> inde a P.
Proof.
elim=> // hd tl IH b P H1 H2.
apply incl_cons_inv_L in H2.
case: H2 => H2 H3.
rewrite /inde => s h x v /= [].
- move=> ?; subst hd; by apply H1.
- move=> x_tl; by apply (IH _ _ H1 H3).
Qed.

Lemma In_inde : forall l y f, List.In y l -> inde l f -> inde (y :: l) f.
Proof.
move=> l y f HIn Hinde s h x v /= [H | H]; split=> Hf.
subst x; by rewrite -(Hinde s h y v HIn).
subst x; by rewrite (Hinde s h y v HIn).
by rewrite -(Hinde s h x v H).
by rewrite (Hinde s h x v H).
Qed.

Lemma inde_rotate : forall l y f, inde (l ++ y :: nil) f -> inde (y :: l) f.
Proof.
move=> l y f Hinde s h x v /= [H|H]; split => Hf.
- subst x.
  have HIn : List.In y (l ++ y::nil) by apply List.in_or_app => /=; auto.
  by rewrite -(Hinde s h y v HIn).
- subst x.
  have HIn : List.In y (l ++ y::nil) by apply List.in_or_app => /=; auto.
  by rewrite (Hinde s h y v HIn).
- have HIn : List.In x (l ++ y::nil) by apply List.in_or_app; simpl; auto.
  by rewrite -(Hinde s h x v HIn).
- have HIn : List.In x (l ++ y::nil) by apply List.in_or_app; simpl; auto.
  by rewrite (Hinde s h x v HIn).
Qed.

Lemma inde_upd_store : forall (P : assert) x z s h,
  inde (x :: nil) P -> P s h -> P (store.upd x z s) h.
Proof. move=> P x z s h H. rewrite (H s h x z) /=; by auto. Qed.

Lemma inde_get : forall l x p, ~ List.In x l -> inde l (fun s h => [x]_s = p).
Proof.
rewrite /inde.
move=> l x0 HP; rewrite /inde => s h x_ v HIn.
split; rewrite store.get_upd //; by move=> Htmp; subst x0.
Qed.

Lemma inde_u2Z_get : forall l x p, ~ List.In x l -> inde l (fun s h => u2Z [x]_s = p).
Proof.
rewrite /inde.
move=> l x0 HP; rewrite /inde => s h x_ v HIn.
split; rewrite store.get_upd //; by move=> Htmp; subst x0.
Qed.

Lemma inde_u2Z_get_plus : forall l x p q, ~ List.In x l -> inde l (fun s h => u2Z [x]_s + q = p).
Proof.
rewrite /inde.
move=> l0 x0 HP; rewrite /inde => s h x_ v HIn.
split; rewrite store.get_upd //; by move=> Htmp; subst x0.
Qed.

Lemma inde_s2Z_get : forall l x p, ~ List.In x l -> inde l (fun s h => s2Z [x]_s = p).
Proof.
rewrite /inde.
move=> l_ x0 HP; rewrite /inde => s h x_ v HIn.
split; rewrite store.get_upd //; by move=> Htmp; subst x0.
Qed.

(* TODO: ajouter a la tactic Inde? *)
Lemma inde_u2Z_fit:
  forall (l : list store.var) (x : store.var) (p : Z),
  ~ List.In x l ->
  inde l
    (fun (s : store.t) (_ : heap.t) => u2Z ([x ]_ s) + p < \B^1).
Proof.
move=> l x p x_l.
rewrite /assert_m.inde => s _ y v y_l.
rewrite store.get_upd //.
move=> abs; subst; by contradiction.
Qed.

Lemma inde_bang : forall l P,
  inde l
    ((fun s h => P s)) ->
  inde l
    (!P).
Proof.
move=> l P H.
rewrite /inde => s h y v y_l; split.
  case => ? ?; subst h.
  split => //.
  apply H => //.
  by exact heap.emp.
case => Ha ?; subst h.
split => //.
apply H in Ha => //.
by exact heap.emp.
Qed.

(* TODO: change the order of the arguments of `>> *)
Lemma inde_u2Z_b_get_R : forall l x p q (b : nat -> int 32 -> int 32) (y : nat) , ~ List.In x l ->
  inde l (fun s h => q + u2Z (b y [x]_s) = p).
Proof.
rewrite /inde.
move=> l x p q b y x_l s _ z v z_l.
by split; rewrite store.get_upd // => abs; subst z.
Qed.

(* TODO: generalizer pour n'importe quelle relation (lt, eq, etc. *)
Lemma inde_u2Z_get_plus_Zlt : forall l x p q, ~ List.In x l -> inde l (fun s h => u2Z [x]_s + q < p).
Proof.
rewrite /inde.
move=> l0 x0 HP => s h x_ v HIn.
split; rewrite store.get_upd //; by move=> Htmp; subst x0.
Qed.

Lemma inde_TT : forall l, inde l TT. Proof. move=> l //. Qed.

Lemma inde_sep_and : forall l (P Q : assert), inde l P -> inde l Q -> inde l (P //\\ Q).
Proof.
rewrite /while.And /inde.
move=> l P Q HP HQ; rewrite /inde => s h x v HIn.
split; move=> [H1 H2]; split.
by rewrite -HP.
by rewrite -HQ.
by rewrite (HP s h x v).
by rewrite (HQ s h x v).
Qed.

Lemma inde_and : forall l P (Q : assert),
  inde l P -> inde l Q -> inde l (fun s h => P s h /\ Q s h).
Proof.
rewrite /inde.
move=> l0 P Q HP HQ; rewrite /inde => s h x_ v HIn.
split; move=> [H1 H2]; split.
by rewrite -HP.
by rewrite -HQ.
by rewrite (HP s h x_ v).
by rewrite (HQ s h x_ v).
Qed.

Lemma inde_imp : forall (l : list reg) (P : Prop) (Q : store.t -> Prop),
  inde l (fun s _ => Q s) ->
  inde l (fun s _ => P -> Q s).
Proof.
move=> l P Q.
rewrite /inde => H s h x v Hx; split => H1 H2.
- rewrite -H //; by apply H1.
- rewrite (H s h x v) //; by apply H1.
Qed.

Lemma inde_imp2 : forall l P Q , inde l P -> inde l Q -> inde l (fun s h => P s h -> Q s h).
Proof.
move=> l P Q indeP indeQ.
rewrite /inde => s h x v x_l; split.
move=> H.
by rewrite -(indeP s h x v x_l) -(indeQ s h x v x_l).
by rewrite (indeP s h x v x_l) (indeQ s h x v x_l).
Qed.

Lemma inde_exists : forall l P,
  (forall y, assert_m.inde l (fun st h => P st h y)) ->
  assert_m.inde l (fun st h => exists y : int 32, P st h y).
Proof.
move=> l P H.
rewrite /assert_m.inde => st h x z z_l; split; case => y P_y; exists y.
- by rewrite -(H y).
- by rewrite (H y st h x z).
Qed.

Lemma inde_sep_con : forall l (P Q : assert),
  inde l P -> inde l Q -> inde l (P ** Q).
Proof.
move=> l P Q HP HQ; rewrite /inde => s h x v HIn.
split; move=> [h1 [h2 [H1 [H2 [H3 H4]]]]]; exists h1; exists h2; repeat (split => //).
by rewrite -(HP s h1).
by rewrite -(HQ s h2).
by rewrite (HP s h1 x v).
by rewrite (HQ s h2 x v).
Qed.

Lemma inde_emp : forall l, inde l emp.
Proof.
move=> l; rewrite /inde => s h x v x_l; split => H; red in H; by subst.
Qed.

Lemma inde_mapsto_int_e : forall e l v, disj (vars e) l -> inde l (e |~> int_e v).
Proof.
elim.
- move=> g l v H [s m] h x v' HIn; split => /=.
  + case: ifP => // xr0.
    apply mapsto_ext => //=.
    case: ifP => // gr0.
    rewrite store.get_upd_p //.
    move=> ?; subst x; case: (H g) => _; move/(_ HIn) => /=; tauto.
  + case: ifP => // xr0.
    apply mapsto_ext => //=.
    case: ifP => // gr0.
    rewrite store.get_upd_p //.
    move=> ?; subst x; case: (H g) => _; move/(_ HIn) => /=; tauto.
- done.
- move=> e IHe e' IHe' l v /= H [s m] h g v' HIn; split => /=.
  + case : ifP => // gr0.
    apply mapsto_ext => //=.
    case/disj_app_inv : H => H1 H3.
    rewrite eval_upd'; last by move=> H2; case: (H1 g); move/(_ H2); tauto.
    rewrite eval_upd' //; last by move=> H2; case: (H3 g); move/(_ H2); tauto.
  + case: ifP => // gr0.
    apply mapsto_ext => //=.
    case/disj_app_inv: H => H1 H3.
    rewrite eval_upd'; last by move=> H2; case: (H1 g); move/(_ H2); tauto.
    rewrite eval_upd' //; last by move=> H2; case: (H3 g); move/(_ H2); tauto.
- move=> e IHe l v H [s m] h x v' HIn; split => /=.
  + case: ifP => // xr0.
    apply mapsto_ext => //=.
    rewrite eval_upd' //; last by move=> H2; case: (H x); move/(_ H2); tauto.
  + case: ifP => // xr0.
    apply mapsto_ext => //=.
    rewrite eval_upd' //; last by move=> H2; case: (H x); move/(_ H2); tauto.
Qed.

Lemma inde_mapstos : forall v l e, disj (vars e) l -> inde l (e |--> v).
Proof.
elim.
- move=> l e Hinter s h x v Hx /=; split.
  + case=> H1 H2; rewrite /emp in H2; subst h; split; last by done.
    rewrite eval_upd //.
    by apply disj_not_In with l.
  + case=> H1 H2; rewrite /emp in H2; subst h; split; last by done.
    rewrite eval_upd // in H1.
    by apply disj_not_In with l.
- move=> // hd tl IH l e H /=.
  apply inde_sep_con => //.
  + by apply inde_mapsto_int_e.
    apply IH => //=.
    by rewrite cats0.
Qed.

(* specializations of inde_mapstos, for use in a tactic *)
Lemma inde_mapstos_var_e v l a : ~ List.In a l -> inde l (var_e a |--> v).
Proof.
move=> H; apply inde_mapstos => /=.
apply disj_cons_L; by [apply disj_nil_L | done].
Qed.

Lemma inde_mapstos_int_e v l a : inde l (int_e a |--> v).
Proof. move=> H; apply inde_mapstos => /=; by apply disj_nil_L. Qed.

(** inde_mult P  iff  the truth of assertion P does not depend on the multiplier *)
Definition inde_mult (P : assert) :=
  forall s h, (forall m m', P (s,m) h <-> P (s,m') h).

Lemma inde_mult_TT : inde_mult TT. Proof. done. Qed.

Lemma inde_mult_sep_con : forall (P Q : assert),
  inde_mult P -> inde_mult Q -> inde_mult (P ** Q).
Proof.
move=> P Q HP HQ s h m m'; split; move=> [h1 [h2 [H1 [H2 [H3 H4]]]]]; exists h1; exists h2; repeat (split => //).
by rewrite -(HP s h1 m).
by rewrite -(HQ s h2 m).
by rewrite (HP s h1 m m').
by rewrite (HQ s h2 m m').
Qed.

Lemma inde_mult_sep_and P Q : inde_mult P -> inde_mult Q -> inde_mult (P //\\ Q).
Proof.
rewrite /inde_mult /while.And => HP HQ s h m m'; split; case=> HP' HQ'.
split; by [rewrite -(HP _ _ m _) | rewrite -(HQ _ _ m _)].
split; by [rewrite (HP _ _ _ m') | rewrite (HQ _ _ _ m')].
Qed.

Lemma inde_mult_mapsto a v : inde_mult (a |~> v).
Proof. move=>  h m m'; split; apply mapsto_ext => //; by apply eval_inde_multiplier. Qed.

Lemma inde_mult_mapstos a v : inde_mult (a |--> v).
Proof.
move=> s h m m'; split; apply mapstos_ext.
by apply eval_inde_multiplier.
by apply eval_inde_multiplier.
Qed.

Lemma inde_mult_maddu : forall (P : assert) p s h, inde_mult P ->
  P s h -> P (store.maddu_op p s) h.
Proof. move=> P p [s m] h HP HP'. by rewrite -(HP s h m). Qed.

Lemma inde_mult_mflhxu_op : forall (P : assert) s h,
  inde_mult P  ->  P s h  ->  P (store.mflhxu_op s) h.
Proof. move=> P [s m] h HP HP'. by rewrite -(HP s  h m). Qed.

Lemma inde_mult_msubu : forall (P : assert) p s h,
  inde_mult P  ->  P s h  ->  P (store.msubu_op p s) h.
Proof. move=> P p [s m] h HP HP'. by rewrite -(HP s h m). Qed.

Lemma inde_mult_mtlo (P : assert) p : forall s h,
  inde_mult P -> P s h -> P (store.mtlo_op p s) h.
Proof. move=> [s [a [hi lo]]] h HP HP' /=; by rewrite -(HP s h (a, (hi, lo))). Qed.

Lemma inde_mult_mthi (P : assert) p : forall s h,
  inde_mult P -> P s h -> P (store.mthi_op p s) h.
Proof. move=> [s [a [hi lo]]] h HP HP'; by rewrite -(HP s h (a, (hi ,lo))). Qed.

Lemma inde_mult_multu (P : assert) : forall p s h,
  inde_mult P -> P s h -> P (store.multu_op p s) h.
Proof. move=> p [s m] h HP HP'. by rewrite -(HP s h m). Qed.

Lemma inde_mult_and (P Q : assert) : inde_mult P -> inde_mult Q ->
  inde_mult (fun s h => P s h /\ Q s h).
Proof.
move=> HP HQ s h m m'; split; case=> [H1 H2]; split.
by rewrite (HP _ _ _ m).
by rewrite (HQ _ _ _ m).
by rewrite (HP _ _ _ m').
by rewrite (HQ _ _ _ m').
Qed.

End assert_m.

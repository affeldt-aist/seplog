(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Classical Epsilon.
From mathcomp Require Import ssreflect ssrbool ssrnat seq.
Require Import Init_ext ZArith_ext ssrZ.
Require Import machine_int.
Import MachineInt.
Require Import mips_bipl.
Export mips_bipl.
Import expr_m.
Require Import while.

(** * Operational semantics *)

Declare Scope mips_cmd_scope.
Declare Scope goto_cmd_scope.

Local Close Scope positive_scope.
Local Open Scope heap_scope.

(** The syntax of one-step, non-branching instructions is formalized as a
(non-recursive) inductive type. The type constructors have the same
name as their SmartMIPS counterparts. As usual with MIPS, instructions
with suffix ``u'' do not trap on overflow and instructions with prefix
``m'' (%\coqdocvar{maddu}%#maddu#, %\coqdocvar{mflhxu}%#mflhxu#, etc.) use the multiplier.
In %\coqdocvar{lw}%#lw#, %\coqdocvar{lwxs}%#lwxs#, and
%\coqdocvar{sw}%#sw#, the second argument is the index, the third one
is the base.
%\coqdocvar{lwxs}%#lwxs# loads words using scaled indexed addressing. *)
Definition immediate := int 16.
Definition shifta := int 5.
Inductive cmd0 : Type :=
| nop : 	cmd0
| add : 	reg -> reg -> reg -> cmd0
| addi : 	reg -> reg -> immediate -> cmd0
| addiu : 	reg -> reg -> immediate -> cmd0
| addu : 	reg -> reg -> reg -> cmd0
| cmd_and : 	reg -> reg -> reg -> cmd0
| andi :	reg -> reg -> immediate -> cmd0
| lw 	: 	reg -> immediate -> reg -> cmd0
| lwxs : 	reg -> reg -> reg -> cmd0
| maddu : 	reg -> reg -> cmd0
| mfhi : 	reg -> cmd0
| mflhxu : 	reg -> cmd0
| mflo : 	reg -> cmd0
| movn :	reg -> reg -> reg -> cmd0
| movz :	reg -> reg -> reg -> cmd0
| msubu : 	reg -> reg -> cmd0
| mthi : 	reg -> cmd0
| mtlo : 	reg -> cmd0
| multu : 	reg -> reg -> cmd0
| nor : 	reg -> reg -> reg -> cmd0
| cmd_or :	reg -> reg -> reg -> cmd0
| sll : 	reg -> reg -> shifta -> cmd0
| sllv : 	reg -> reg -> reg -> cmd0
| sltu : 	reg -> reg -> reg -> cmd0
| sra :         reg -> reg -> shifta -> cmd0
| srl :		reg -> reg -> shifta -> cmd0
| srlv :	reg -> reg -> reg -> cmd0
| subu :	reg -> reg -> reg -> cmd0
| sw :	 	reg -> immediate -> reg -> cmd0
| xor : 	reg -> reg -> reg -> cmd0
| xori :	reg -> reg -> immediate -> cmd0.

Lemma cmd0_dec_nop : forall c, { c = nop } + { c <> nop }.
Proof. elim=> //; (left; reflexivity) || (move=> *; right=> X //). Qed.

Local Open Scope mips_expr_scope.

(** The state of a SmartMIPS processor is modeled as a tuple of a
store of general-purpose registers, an integer multiplier, and a heap
(the mutable memory): *)

Definition state := (store.t * heap.t)%type.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.

Delimit Scope mips_cmd_scope with mips_cmd.
Local Open Scope mips_cmd_scope.

(** We first equip the one-step, non-branching SmartMIPS instructions
(those instructions that modify the state and just increment the program
counter) with an operational semantics.
We use an option type for states to represent error-states.
Instructions suffixed with "u" does not trap on overflow. *)
Reserved Notation "s '--' c '---->' t" (at level 74 , no associativity).

Inductive exec0 : option state -> cmd0 -> option state -> Prop :=
| exec0_nop : forall st, |_ st _| -- nop ----> |_ st _|
| exec0_add : forall s h rd rs rt,
  - 2 ^^ 31 <= s2Z [rs]_s + s2Z [rt]_s < 2 ^^ 31 ->
  |_ s, h _| -- add rd rs rt ----> |_ store.upd rd ([rs]_s `+ [rt]_s) s, h _|
| exec0_add_error : forall s h rd rs rt,
  ~ (- 2 ^^ 31 <= s2Z [rs]_s + s2Z [rt]_s < 2 ^^ 31) ->
  |_ s, h _| -- add rd rs rt ----> None
| exec0_addi : forall s h rt rs imm,
  - 2 ^^ 31 <= s2Z [rs]_s + s2Z (sext 16 imm) < 2 ^^ 31 ->
  |_ s, h _| -- addi rt rs imm ----> |_ store.upd rt ([rs]_s `+ sext 16 imm) s, h _|
| exec0_addi_error : forall s h rt rs imm,
  ~ (- 2 ^^ 31 <= s2Z ([rs]_s) + s2Z (sext 16 imm) < 2 ^^ 31) ->
  |_ s, h _| -- addi rt rs imm ----> None
| exec0_addiu : forall s h rt rs imm,
  |_ s, h _| -- addiu rt rs imm ----> |_ store.upd rt ([rs]_s `+ sext 16 imm) s, h _|
| exec0_addu : forall s h rd rs rt,
  |_ s, h _| -- addu rd rs rt ----> |_ store.upd rd ([rs]_s `+ [rt]_s) s, h _|
| exec0_and : forall s h rd rs rt,
  |_ s, h _| -- cmd_and rd rs rt ----> |_ store.upd rd ([rs]_s `& [rt]_s) s, h _|
| exec0_andi : forall s h rt rs imm,
  |_ s, h _| -- andi rt rs imm ----> |_ store.upd rt ([rs]_s `& zext 16 imm) s, h _|
| exec0_lw : forall s h rt (off : immediate) base p z,
  u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat p -> heap.get p h = |_ z _| ->
  |_ s, h _| -- lw rt off base ----> |_ store.upd rt z s, h _|
| exec0_lw_error : forall s h rt (off : immediate) base,
  ~ (exists l, u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat l /\ exists z, heap.get l h = |_ z _|) ->
  |_ s, h _| -- lw rt off base ----> None
| exec0_lwxs : forall s h rt idx base p z,
  u2Z ([base]_s `+ ([idx]_s `<< 2)) = 4 * Z_of_nat p -> heap.get p h = |_ z _| ->
  |_ s, h _| -- lwxs rt idx base ----> |_ store.upd rt z s, h _|
| exec0_lwxs_error : forall s h rt idx base,
  ~ (exists l, u2Z ([base]_s `+ ([idx]_s `<< 2)) = 4 * Z_of_nat l /\ exists z, heap.get l h = |_ z _|) ->
  |_ s, h _| -- lwxs rt idx base ----> None
| exec0_maddu : forall s h rs rt,
  |_ s, h _| -- maddu rs rt ----> |_ store.maddu_op ([rs]_s `* [rt]_s) s, h _|
| exec0_mfhi : forall s h rd,
  |_ s, h _| -- mfhi rd ----> |_ store.upd rd (store.hi s) s, h _|
| exec0_mflhxu : forall s h rd,
  |_ s, h _| -- mflhxu rd ----> |_ store.mflhxu_op (store.upd rd (store.lo s) s), h _|
| exec0_mflo : forall s h rd,
  |_ s, h _| -- mflo rd ----> |_ store.upd rd (store.lo s) s, h _|
| exec0_movn_true : forall s h rd rs rt,
  [rt]_s <> zero32 ->
  |_ s, h _| -- movn rd rs rt ----> |_ store.upd rd [rs]_s s, h _|
| exec0_movn_false : forall s h rd rs rt,
  [rt]_s = zero32 -> |_ s, h _| -- movn rd rs rt ----> |_ s,  h _|
| exec0_movz_true : forall s h rd rs rt,
  [rt]_s = zero32 ->
  |_ s, h _| -- movz rd rs rt ----> |_ store.upd rd [rs]_s s, h _|
| exec0_movz_false : forall s h rd rs rt,
  [rt]_s <> zero32 -> |_ s, h _| -- movz rd rs rt ----> |_ s, h _|
| exec0_msubu : forall s h rs rt,
  |_ s, h _| -- msubu rs rt ----> |_ store.msubu_op ([rs]_s `* [rt]_s) s, h _|
| exec0_mthi : forall s h rs,
  |_ s, h _| -- mthi rs ----> |_ store.mthi_op [rs]_s s, h _|
| exec0_mtlo : forall s h rs,
  |_ s, h _| -- mtlo rs ----> |_ store.mtlo_op [rs]_s s, h _|
| exec0_multu : forall s h rs rt,
  |_ s, h _| -- multu rs rt ----> |_ store.multu_op ([rs]_s `* [rt]_s) s, h _|
| exec0_nor : forall s h rd rs rt,
  |_ s, h _| -- nor rd rs rt ----> |_ store.upd rd (int_not ([rs]_s `|` [rt]_s)) s, h _|
| exec0_or : forall s h rd rs rt,
  |_ s, h _| -- cmd_or rd rs rt ----> |_ store.upd rd ([rs]_s `|` [rt]_s) s, h _|
| exec0_sll : forall s h rx ry sa,
  |_ s, h _| -- sll rx ry sa ----> |_ store.upd rx ([ry]_s `<< '|u2Z sa|) s, h _|
| exec0_sllv : forall s h rd rt rs,
  |_ s, h _| -- sllv rd rt rs ----> |_ store.upd rd ([rt]_s `<< '|u2Z ([rs]_s `% 5)|) s, h _|
| exec0_sltu : forall s h rd rs rt flag,
  flag = (if Zlt_bool (u2Z [rs]_s) (u2Z [rt]_s) then one32 else zero32) ->
  |_ s, h _| -- sltu rd rs rt ----> |_ store.upd rd flag s, h _|
| exec0_sra : forall s h rd rt sa,
  |_ s, h _| -- sra rd rt sa ----> |_ store.upd rd (shra '|u2Z sa| [rt]_s) s, h _|
| exec0_srl : forall s h rd rt sa,
  |_ s, h _| -- srl rd rt sa ----> |_ store.upd rd ([rt]_s `>> '|u2Z sa|) s, h _|
| exec0_srlv : forall s h rd rt rs,
  |_ s, h _| -- srlv rd rt rs ----> |_ store.upd rd ([rt]_s `>> '|u2Z ([rs]_s `% 5)|) s, h _|
| exec0_subu : forall s h rd rs rt,
  |_ s, h _| -- subu rd rs rt ----> |_ store.upd rd ([rs]_s `+ (cplt2 [rt]_s)) s, h _|
| exec0_sw : forall s h rt (off : immediate) base p,
  u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat p -> (exists z, heap.get p h = |_ z _|) ->
  |_ s, h _| -- sw rt off base ----> |_ s, heap.upd p [rt]_s h _|
| exec0_sw_err : forall s h rt (off : immediate) base,
  ~ (exists l, u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat l /\ exists z, heap.get l h = |_ z _|) ->
  |_ s, h _| -- sw rt off base ----> None
| exec0_xor : forall s h rd rs rt,
  |_ s, h _| -- xor rd rs rt ----> |_ store.upd rd (int_xor [rs]_s [rt]_s) s, h _|
| exec0_xori : forall s h rt rs imm,
  |_ s, h _| -- xori rt rs imm ----> |_ store.upd rt (int_xor [rs]_s (zext 16 imm)) s, h _|
where "s -- c ----> t" := (exec0 s c t) : mips_cmd_scope.

Lemma exec0_nop_inv s s' : |_ s _| -- nop ----> s' -> s' = |_ s _|.
Proof. by inversion 1. Qed.

Lemma exec0_addi_inv s h rt rs imm s' : |_ s, h _| -- addi rt rs imm ----> s' ->
  - 2 ^^ 31 <= s2Z [rs]_s + s2Z (sext 16 imm) < 2 ^^ 31 /\
  s' = |_ store.upd rt ([rs]_s `+ sext 16 imm) s, h _|
  \/
  ~ (- 2 ^^ 31 <= s2Z [rs]_s + s2Z (sext 16 imm) < 2 ^^ 31) /\
  s' = None.
Proof. inversion 1; tauto. Qed.

Lemma exec0_addiu_inv s h rt rs imm s' : |_ s, h _| -- addiu rt rs imm ----> s' ->
  s' = |_ store.upd rt ([rs]_s `+ sext 16 imm) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_add_inv s h rd rs rt s' : |_ s, h _| -- add rd rs rt ----> s' ->
  - 2 ^^ 31 <= s2Z [rs]_s + s2Z [rt]_s < 2 ^^ 31 /\
  s' = |_ store.upd rd ([rs]_s `+ [rt]_s) s, h _|
  \/
  ~ (- 2 ^^ 31 <= s2Z [rs]_s + s2Z [rt]_s < 2 ^^ 31) /\
  s' = None.
Proof. inversion 1; tauto. Qed.

Lemma exec0_addu_inv s h rd rs rt s' : |_ s, h _| -- addu rd rs rt ----> s' ->
  s' = |_ store.upd rd ([rs]_s `+ [rt]_s) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_and_inv s h rd rs rt s' : |_ s, h _| -- cmd_and rd rs rt ----> s' ->
  s' = |_ store.upd rd ([rs]_s `& [rt]_s) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_andi_inv s h rt rs imm s' : |_ s, h _| -- andi rt rs imm ----> s' ->
  s' = |_ store.upd rt ([rs]_s `& zext 16 imm) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_lw_inv s h rt (off : immediate) base s' :
  |_ s, h _| -- lw rt off base ----> s' ->
  (exists p, u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat p /\ exists z, heap.get p h = |_ z _| /\
    s' = |_ store.upd rt z s, h _|)
    \/
  ~ (exists l, u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat l /\ exists z, heap.get l h = |_ z _|) /\
  s' = None.
Proof.
inversion 1; subst.
left; exists p; split=> //; by exists z.
by right.
Qed.

Lemma exec0_lwxs_inv s h rt idx base s' :
  |_ s, h _| -- lwxs rt idx base ----> s' ->
  (exists p, u2Z ([base]_s `+ ([idx]_s `<< 2)) = 4 * Z_of_nat p /\ exists z, heap.get p h = |_ z _| /\ s' = |_ store.upd rt z s, h _|)
  \/
  ~ (exists l, u2Z ([base]_s `+ ([idx]_s `<< 2)) = 4 * Z_of_nat l /\ exists z, heap.get l h = |_ z _|) /\ s' = None.
Proof.
inversion 1; subst.
left; exists p; split=> //; by exists z.
by right.
Qed.

Lemma exec0_maddu_inv s h rs rt s' : |_ s, h _| -- maddu rs rt ----> s' ->
  s' = |_ store.maddu_op ([rs]_s `* [rt]_s) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_mfhi_inv s h rd s' : |_ s, h _| -- mfhi rd ----> s' ->
  s' = |_ store.upd rd (store.hi s) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_mflhxu_inv s h rd s' : |_ s, h _| -- mflhxu rd ----> s' ->
  s' = |_ store.mflhxu_op (store.upd rd (store.lo s) s), h _|.
Proof. by inversion 1. Qed.

Lemma exec0_mflo_inv s h rd s' : |_ s, h _| -- mflo rd ----> s' ->
  s' = |_ store.upd rd (store.lo s) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_movn_inv s h rd rs rt s' : |_ s, h _| -- movn rd rs rt ----> s' ->
  [rt]_s <> zero32 /\ s' = |_ store.upd rd [rs]_s s, h _| \/
  [rt]_s = zero32 /\ s' = |_ s,  h _|.
Proof. by inversion 1; auto. Qed.

Lemma exec0_movz_inv s h rd rs rt s' : |_ s, h _| -- movz rd rs rt ----> s' ->
  [rt]_s = zero32 /\ s' = |_ store.upd rd [rs]_s s, h _| \/
  [rt]_s <> zero32 /\ s' = |_ s, h _|.
Proof. by inversion 1; auto. Qed.

Lemma exec0_msubu_inv s h rs rt s' : |_ s, h _| -- msubu rs rt ----> s' ->
  s' = |_ store.msubu_op ([rs]_s `* [rt]_s) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_mthi_inv s h rs s' : |_ s, h _| -- mthi rs ----> s' ->
  s' = |_ store.mthi_op [rs]_s s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_mtlo_inv s h rs s' : |_ s, h _| -- mtlo rs ----> s' ->
  s' = |_ store.mtlo_op [rs]_s s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_multu_inv  s h rs rt s' : |_ s, h _| -- multu rs rt ----> s' ->
  s' = |_ store.multu_op ([rs]_s `* [rt]_s) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_nor_inv s h rd rs rt s' : |_ s, h _| -- nor rd rs rt ----> s' ->
  s' = |_ store.upd rd (int_not ([rs]_s `|` [rt]_s)) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_or_inv s h rd rs rt s' : |_ s, h _| -- cmd_or rd rs rt ----> s' ->
  s' = |_ store.upd rd ([rs]_s `|` [rt]_s) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_sll_inv s h rx ry sa s' : |_ s, h _| -- sll rx ry sa ----> s' ->
  s' = |_ store.upd rx ([ry]_s `<< '|u2Z sa|) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_sllv_inv  s h rd rt rs s' : |_ s, h _| -- sllv rd rt rs ----> s' ->
  s' = |_ store.upd rd ([rt]_s `<< '|u2Z ([rs]_s `% 5)|) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_sltu_inv s h rd rs rt s' : |_ s, h _| -- sltu rd rs rt ----> s' ->
  s' = |_ store.upd rd (if u2Z [rs]_s <? u2Z [rt]_s then one32 else zero32) s, h _|.
Proof. by inversion 1; subst. Qed.

Lemma exec0_sra_inv s h rd rt sa s' : |_ s, h _| -- sra rd rt sa ----> s' ->
  s' = |_ store.upd rd (shra '|u2Z sa| [rt]_s) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_srl_inv s h rd rt sa s' : |_ s, h _| -- srl rd rt sa ----> s' ->
  s' = |_ store.upd rd ([rt]_s `>> '|u2Z sa|) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_srlv_inv s h rd rt rs s' : |_ s, h _| -- srlv rd rt rs ----> s' ->
  s' = |_ store.upd rd ([rt]_s `>> '|u2Z ([rs]_s `% 5)|) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_subu_inv s h rd rs rt s' : |_ s, h _| -- subu rd rs rt ----> s' ->
  s' = |_ store.upd rd ([rs]_s `+ (cplt2 [rt]_s)) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_sw_inv s h rt (off : immediate) base s' :
  Some (s,h) -- sw rt off base ----> s' ->
  (exists p, u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat p /\ exists z, heap.get p h = Some z /\ s' = Some (s,heap.upd p [rt]_s h))
  \/
  ~ (exists l, u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat l /\ exists z, heap.get l h = Some z) /\ s' = None.
Proof.
inversion 1; subst.
- left; exists p; split=> //.
  case: H7 => z H7.
  by exists z.
- by right.
Qed.

Lemma exec0_xor_inv s h rd rs rt s' : |_ s, h _| -- xor rd rs rt ----> s' ->
  s' = |_ store.upd rd ([rs]_s `(+) [rt]_s) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_xori_inv s h rt rs imm s' : |_ s, h _| -- xori rt rs imm ----> s' ->
  s' = |_ store.upd rt ([rs]_s `(+) zext 16 imm) s, h _|.
Proof. by inversion 1. Qed.

Lemma exec0_deter st c st' :
  st -- c ----> st' -> forall st'', st -- c ----> st'' -> st' = st''.
Proof.
elim=> //; clear st c st'.
- move=> st st'; by move/exec0_nop_inv.
- (* add *) move=> s h rd rs rt H s'.
  case/exec0_add_inv; last by tauto.
  by case=> _ ->.
- (* add error *) move=> s h rt rs imm H s'.
  case/exec0_add_inv; first by tauto.
  by case.
- move=> s h rt rs imm H s'.
  case/exec0_addi_inv; last by tauto.
  by case=> _ ->.
- move=> s h rt rs imm H s'.
  case/exec0_addi_inv; first by tauto.
  by case.
- move=> s h rt rs imm s'; by move/exec0_addiu_inv.
- move=> s h rd rs rt s'; by move/exec0_addu_inv.
- move=> s h rd rs rt s'; by move/exec0_and_inv.
- move=> s h rd rs rt s'; by move/exec0_andi_inv.
- (* lw *) move=> s h rt off base p z Hp Hz s'.
  case/exec0_lw_inv.
  move=> [p' [Hp' [z' [Hz' Hs']]]].
  have -> // : z = z'.
    have X : p = p' by lia.
    subst.
    rewrite Hz' in Hz; by case: Hz.
  move=> X.
  exfalso.
  apply X.
  exists p; split => //; by exists z.
- (* lw error *) move=> s h rt off base X s'.
  case/exec0_lw_inv.
  move=> [p [Hp [z [Hz Hs']]]].
  exfalso.
    apply X.
    exists p; split => //; by exists z.
  by case.
- move=> s h rt off base p z Hp Hz s'.
  case/exec0_lwxs_inv.
  move=> [p' [Hp' [z' [Hz' Hs']]]].
  have ->// : z = z'.
    have X : p = p' by lia.
    subst.
    rewrite Hz' in Hz; by case: Hz.
  move=> X.
  exfalso.
  apply X.
  exists p; split => //; by exists z.
- move=> s h rt off base X s'.
  case/exec0_lwxs_inv.
  move=> [p [Hp [z [Hz Hs']]]].
  exfalso.
    apply X.
    exists p; split => //; by exists z.
  by case.
- move=> s h rs rt s'; by move/exec0_maddu_inv.
- move=> s h rd s'; by move/exec0_mfhi_inv.
- move=> s h rd s'; by move/exec0_mflhxu_inv.
- move=> s h rd s'; by move/exec0_mflo_inv.
- (* movn true *) move=> s h rd rs rt H st''.
  case/exec0_movn_inv.
  case=> _ -> //.
  by case.
- (* movn false *) move=> s h rd rs rt H st''.
  case/exec0_movn_inv.
  case=> //.
  by case=> _ ->.
- (* movz true *) move=> s h rd rs rt H' st''.
  case/exec0_movz_inv.
  case=> _ -> //.
  by case.
- (* movz false *) move=> s h rd rs rt H' st''.
  case/exec0_movz_inv.
  case=> //.
  by case=> _ ->.
- move=> s h rs rt st''; by move/exec0_msubu_inv.
- move=> s h rs st''; by move/exec0_mthi_inv.
- move=> s h rs st''; by move/exec0_mtlo_inv.
- move=> s h rs rt st''; by move/exec0_multu_inv.
- move=> s h rd rs rt st''; by move/exec0_nor_inv.
- move=> s h rd rs rt st''; by move/exec0_or_inv.
- move=> s h rx ry sa st''; by move/exec0_sll_inv.
- move=> s h rd rs st st''; by move/exec0_sllv_inv.
- move=> s h rd rs rt flag H' st''; by move/exec0_sltu_inv; subst.
- move=> s h rd rt sa st''; by move/exec0_sra_inv.
- move=> s h rd rt sa st''; by move/exec0_srl_inv.
- move=> s h rd rt rs st''; by move/exec0_srlv_inv.
- move=> s h rd rs rt st''; by move/exec0_subu_inv; subst.
- (* sw *) move=> s h rt off base p Hp [z Hz] st''.
  case/exec0_sw_inv.
  move=> [p' [Hp' [z' [Hz' ->]]]].
  have ->// : p = p' by lia.
  move=> X.
  exfalso.
  apply X.
  exists p; split => //; by exists z.
- (* sw error *) move=> s h rt off base X s'.
  case/exec0_sw_inv.
  move=> [p [Hp [z [Hz Hs']]]].
  exfalso.
    apply X.
    exists p; split => //; by exists z.
  by case.
- move=> s h rd rs rt st''; by move/exec0_xor_inv.
- move=> s h rt rs imm st''; by move/exec0_xori_inv.
Qed.

(** The syntax of %\while\ %#While# programs is encoded as an inductive type parameterized 
by boolean tests and one-step, non-branching intructions: *)

Coercion cmd_cmd0_coercion := @while.cmd_cmd0 cmd0 expr_b.

Notation "c ; d" := (while.seq c d) (at level 81, right associativity, format
"'[v' '[' c ']'  ';' '//' '[' d ']' ']'") : mips_cmd_scope.

Notation "'If' e 'Then' c1 'Else' c2" := (while.ifte e c1 c2) 
  (at level 200, right associativity, format 
"'[v' '[' 'If'  e  'Then' ']' '//'   '[' c1 ']' '//' '[' 'Else' ']' '//'   '[' c2 ']' '//' ']'") : mips_cmd_scope.

Notation "'If_beq' a ',' b 'Then' x 'Else' y" := (while.ifte (beq a b) x y) (at level 200,
format 
"'[v' '[' 'If_beq'  a ',' b  'Then' ']' '//'   '[' x ']' '//' '[' 'Else' ']' '//'   '[' y ']' '//' ']'"
) : mips_cmd_scope.

Notation "'If_bne' a ',' b 'Then' x 'Else' y" := (while.ifte (bne a b) x y) (at level 200,
format 
"'[v' '[' 'If_bne'  a ',' b  'Then' ']' '//'   '[' x ']' '//' '[' 'Else' ']' '//'   '[' y ']' '//' ']'"
) : mips_cmd_scope.

Notation "'If_bltz' a 'Then' x 'Else' y" := (while.ifte (bltz a) x y) (at level 200,
format 
"'[v' '[' 'If_bltz'  a  'Then' ']' '//'   '[' x ']' '//' '[' 'Else' ']' '//'   '[' y ']' '//' ']'"
) : mips_cmd_scope.

Notation "'If_blez' a 'Then' x 'Else' y" := (while.ifte (blez a) x y) (at level 200,
format 
"'[v' '[' 'If_blez'  a  'Then' ']' '//'   '[' x ']' '//' '[' 'Else' ']' '//'   '[' y ']' '//' ']'"
) : mips_cmd_scope.

Notation "'If_bgtz' a 'Then' x 'Else' y" := (while.ifte (bgtz a) x y) (at level 200,
format 
"'[v' '[' 'If_bgtz'  a  'Then' ']' '//'   '[' x ']' '//' '[' 'Else' ']' '//'   '[' y ']' '//' ']'"
) : mips_cmd_scope.

Notation "'If_bgez' a 'Then' x 'Else' y" := (while.ifte (bgez a) x y) (at level 200,
format 
"'[v' '[' 'If_bgez'  a  'Then' ']' '//'   '[' x ']' '//' '[' 'Else' ']' '//'   '[' y ']' '//' ']'"
) : mips_cmd_scope.

Notation "'While' e '{{' c '}}' " := (while.while e c) 
  (at level 200, format 
"'[v' 'While'  e  '{{' '//'   '[' c ']' '//' '}}' ']'") : mips_cmd_scope.

Notation "s -- c ---> t" := (@while.exec store.t heap.t _ exec0 _
  (fun eb st => eval_b eb (fst st)) s c t)  (at level 74, no associativity) : mips_cmd_scope.

Lemma from_none0 : forall s (c : cmd0), None -- c ----> s -> s = None.
Proof. by inversion 1. Qed.

Lemma cmd0_terminate : forall (c : cmd0) s, exists s', Some s -- c ----> s'.
Proof.
elim=> //.
- move=> s; exists (Some s); apply exec0_nop.
- (* add *) move=> g g0 g1 [s h].
  case: (classic (-2 ^^ 31 <= s2Z [g0]_s + s2Z [g1]_s < 2 ^^ 31))=> X.
  + eapply ex_intro; by constructor.
  + exists None; by constructor.
- (* addi *) move=> g g0 i [s h].
  case: (classic (- 2 ^^ 31 <= s2Z [g0]_s + s2Z (sext 16 i) < 2 ^^ 31))=> X.
  + eapply ex_intro; by constructor.
  + exists None; by constructor.
- (* addiu *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* addu *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* cmd_and *) move => ? ? ? [s h]; eapply ex_intro; by constructor.
- (* andi *) move => ? ? ? [s h]; eapply ex_intro; by constructor.
- (* lw *) move => g i g0 [s h].
  case: (classic (exists l, u2Z ([g0]_s `+ sext 16 i) = 4 * Z_of_nat l /\ exists z, heap.get l h = Some z)) => X.
  + case: X => l [H [z H']].
    exists (Some (store.upd g z s,h)); by apply (exec0_lw _ _ _ _ _ _ _ H).
  + exists None; by constructor.
- (* lwxs *) move => g g0 g1 [s h].
  case: (classic (exists l, (u2Z ([g1]_s `+ shl 2 [g0]_s) = 4 * Z_of_nat l)%Z /\ (exists z, heap.get l h = Some z))) => X.
  + case: X => l [H [z H']].
    exists (Some (store.upd g z s,h)); by apply (exec0_lwxs _ _ _ _ _ _ _ H).
  + exists None; by constructor.
- (* maddu *) move=> ? ? [s h]; eapply ex_intro; by constructor.
- (* mfhi *) move=> ? [s h]; eapply ex_intro; by constructor.
- (* mflhxu *) move=> ? [s h]; eapply ex_intro; by constructor.
- (* mflo *) move=> ? [s h]; eapply ex_intro; by constructor.
- (* movn *) move=> rd rs rt [s h].
  case: (dec_int [rt]_s zero32) => X.
  + exists (Some (s, h)); by constructor.
  + exists (Some (store.upd rd [rs]_s s,h)); by constructor.
- (* movz *) move=> rd rs rt [s h].
  elim: (dec_int [rt]_s zero32) => X.
  + exists (Some (store.upd rd [rs]_s s,h)); by constructor.
  + exists (Some (s,h)); by constructor.
- (* msubu *) move=> ? ? [s h]; eapply ex_intro; by constructor.
- (* mthi *) move=> ? [s h]; eapply ex_intro; by constructor.
- (* mtlo *) move=> ? [s h]; eapply ex_intro; by constructor.
- (* multu *) move=> ? ? [s h]; eapply ex_intro; by constructor.
- (* nor *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* cmd_or *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* sll *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* sllv *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* sltu *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* sra *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* srl *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* srlv *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* subu *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* sw *) move=> g i g0 [s h].
  case: (classic (exists p,
    u2Z ([g0]_s `+ sext 16 i) = 4 * Z_of_nat p /\
    (exists z, heap.get p h = Some z))) => X.
  + case: X => p [ H1 [z H2]].
    exists (Some (s, heap.upd p [g]_s h)). apply (exec0_sw _ _ _ _ _ _ H1). by exists z.
  + exists None; by constructor.
- (* xor *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
- (* xori *) move=> ? ? ? [s h]; eapply ex_intro; by constructor.
Qed.

Module WMIPS_Semop <: while.WHILE_SEMOP.

Definition store : Type := store.t.
Definition heap : Type := heap.t.
Definition state : Type := (store * heap)%type.

Definition cmd0 : Type := cmd0.
Definition exec0 : option state -> cmd0 -> option state -> Prop := exec0.
Notation "s -- c ----> t" := (exec0 s c t) (at level 74 , no associativity) : goto_cmd_scope.
Local Open Scope goto_cmd_scope.

Definition from_none0 : forall s c, None -- c ----> s -> s = None := from_none0.
Definition cmd0_terminate : forall (c : cmd0) s, exists s', |_ s _| -- c ----> s' := cmd0_terminate.

Local Close Scope goto_cmd_scope.

Definition expr_b : Type := expr_b.
Definition neg : expr_b -> expr_b := neg.
Definition eval_b : expr_b -> state -> bool := fun eb s => eval_b eb (fst s).
Lemma eval_b_neg : forall t s, eval_b (neg t) s = ~~ eval_b t s.
Proof. move=> eb [s h]; rewrite /eval_b /=; by apply eval_b_neg. Qed.
Definition cmd := @while.cmd cmd0 expr_b.
Coercion cmd_cmd0_coercion := @while.cmd_cmd0 cmd0 expr_b.
Definition exec : option state -> cmd -> option state -> Prop :=
  @while.exec store heap cmd0 exec0 expr_b (fun eb s => eval_b eb s).

End WMIPS_Semop.

Module WMIPS_Semop_Deter <: while.WHILE_SEMOP_DETER.

Include WMIPS_Semop.

Definition exec0_deter : forall (st : option state) (c : cmd0) (st' : option state),
  st -- c ----> st' ->
  forall st'',  st -- c ----> st'' -> st' = st'' := exec0_deter.

End WMIPS_Semop_Deter.

Module semop_prop_m := while.While_Semop_Prop WMIPS_Semop.

Lemma exec0_add_not_None s h g g0 g1 : ~ |_ s, h _| -- add g g0 g1 ----> None ->
  - 2 ^^ 31 <= s2Z [g0]_s + s2Z [g1]_s < 2 ^^ 31.
Proof. move=> H; apply NNPP; contradict H; do ! constructor=> //. Qed.

Lemma exec0_addi_not_None s h g g0 i : ~ |_ s, h _| -- addi g g0 i ----> None ->
  - 2 ^^ 31 <= s2Z [g0]_s + s2Z (sext 16 i) < 2 ^^ 31.
Proof. move=> H; apply NNPP. contradict H. do ! constructor=> //. Qed.

Lemma exec0_lw_not_None s h g i g0 : ~ |_ s, h _| -- lw g i g0 ----> None ->
  exists p, u2Z ([ var_e g0 ]e_ s `+ sext 16 i) = 4 * Z_of_nat p /\
    exists z, heap.get p h = Some z.
Proof. move=> H; apply NNPP. contradict H. do ! constructor=> //. Qed.

Lemma exec0_lwxs_not_None s h g g0 g1 : ~ |_ s, h _| -- lwxs g g0 g1 ----> None ->
  exists p, u2Z ([g1]_s `+ ([g0]_s `<< 2)) = 4 * Z_of_nat p /\
    exists z, heap.get p h = Some z.
Proof. move=> H. apply NNPP. contradict H. repeat constructor=> //. Qed.

Lemma exec0_sw_not_None s h g i g0 : ~ |_ s, h _| -- sw g i g0 ----> None ->
  exists p, u2Z ([ var_e g0 ]e_s `+ sext 16 i) = 4 * Z_of_nat p /\
    exists z, heap.get p h = Some z.
Proof. move=> H. apply NNPP. contradict H. repeat constructor=> //. Qed.

Lemma exec0_not_None_to_exec_not_None (s : WMIPS_Semop.store) (h : WMIPS_Semop.heap) (c : cmd0) :
  ~ (|_ s, h _| -- c ---> None) -> ~ |_ s, h _| -- c ----> None.
Proof. move=> H H'. by apply H, while.exec_cmd0. Qed.

Lemma cmd0_terminate' : forall (c : cmd0) s, exists s', Some s -- c ---> s'.
Proof. move=> c s. case: (cmd0_terminate c s) => s' H. exists s'; by apply while.exec_cmd0. Qed.

Lemma exists_exec_seq_assoc'_P s c0 c1 c2 P :
  {s' | s -- c0 ; c1 ; c2 ---> s' /\ P s'} ->
  {s' | s -- (c0 ; c1) ; c2 ---> s' /\ P s'}.
Proof.
move=> [s' H]. exists s'.
split; last by tauto.
apply semop_prop_m.exec_seq_assoc'; tauto.
Qed.

Lemma exists_addiu_seq rt rs (i : int 16) c s h :
  {s' | Some (store.upd rt ([rs]_s `+ sext 16 i) s, h) -- c ---> s'} ->
  {s' | Some (s, h) -- addiu rt rs i; c ---> s'}.
Proof.
move=> [s' H].
exists s'; eapply while.exec_seq; eauto.
do 2 constructor.
Qed.

Lemma exists_nop s : { s' | Some s -- nop ---> s' }.
Proof. exists (Some s); by do 2 constructor. Qed.

Lemma exists_nop_P s (P : state -> Prop) : P s ->
  {s' | Some s -- nop ---> s' /\ forall st, s' = Some st -> P st}.
Proof.
move=> HP; exists (Some s); split.
by do 2 constructor.
by move=> st [] <-.
Qed.

Lemma exists_addiu rt rs (imm : int 16) s h : {s' | Some (s, h) -- addiu rt rs imm ---> s'}.
Proof.
exists (Some (store.upd rt ([rs]_s `+ sext 16 imm) s, h)).
by do 2 constructor.
Qed.

Lemma exists_addiu_P rt rs (imm : int 16) s h (P : state -> Prop) :
  P (store.upd rt ([rs]_s `+ sext 16 imm) s, h) ->
  {s' | Some (s, h) -- addiu rt rs imm ---> s' /\ forall st, s' = Some st -> P st}.
Proof.
move=> H.
exists (Some (store.upd rt ([rs]_s `+ sext 16 imm) s, h)); split => //.
do 2 constructor.
move=> st [] <- //.
Qed.

Lemma exists_addiu_seq_P rt rs (imm : int 16) c s h P :
  {s' | Some (store.upd rt ([rs]_s `+ sext 16 imm) s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- addiu rt rs imm ; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //.
eapply while.exec_seq; eauto.
by do 2 constructor.
Qed.

Lemma exists_and_P rd rs rt s h (P : state -> Prop) :
  P (store.upd rd ([rs]_s `& [rt]_s) s, h) ->
  {s' | Some (s, h) -- cmd_and rd rs rt ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> HP.
exists (Some (store.upd rd ([rs]_s `& [rt]_s) s, h)); split => //.
by do 2 constructor.
by move=> st [] <-.
Qed.

Lemma exists_andi_seq_P rt rs (imm : int 16) c s h P :
  {s' | Some (store.upd rt ([rs]_s `& zext 16 imm) s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- andi rt rs imm; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //.
eapply while.exec_seq; eauto.
by do 2 constructor.
Qed.

Lemma exists_mthi_seq_P rs c s h P :
  {s' | Some (store.mthi_op [rs]_s s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- mthi rs; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //.
eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_mflhxu_seq_P rd c s h P :
  {s' | Some (store.mflhxu_op (store.upd rd (store.lo s) s), h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- mflhxu rd; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //.
eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_mtlo_P rs s h (P : state -> Prop) :
  P (store.mtlo_op [rs]_s s, h) ->
  {s' | Some (s, h) -- mtlo rs ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> H.
exists (Some (store.mtlo_op [rs]_s s, h)); split => //.
do 2 constructor.
by move=> st [] <-.
Qed.

Lemma exists_sll_P rx ry sa s h (P : state -> Prop) :
  P (store.upd rx ([ry]_s `<< '|u2Z sa|) s, h)%mips_expr ->
  {s' | (Some (s, h) -- sll rx ry sa ---> s') /\ (forall st, s' = Some st -> P st)}%mips_cmd.
Proof.
move=> HP.
eexists.
split.
by do 2 constructor.
move=> st.
by case=> <-.
Qed.

Lemma exists_sll_seq_P rx ry sa c s h P :
  {s' | |_ store.upd rx ([ry]_s `<< '|u2Z sa|) s, h _| -- c ---> s' /\ P s'} ->
  {s' | |_ s, h _| -- sll rx ry sa; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //.
eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_sllv_seq_P rd rt rs c s h P :
  {s' | |_ store.upd rd ([rt]_s `<< '|u2Z ([rs]_s `% 5)|) s, h _| -- c ---> s' /\ P s'} ->
  {s' | |_ s, h _| -- sllv rd rt rs; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //.
eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_sra_seq_P rd rt sa c s h P :
  {s' | |_ store.upd rd (shra '|u2Z sa| [rt]_s) s, h _| -- c ---> s' /\ P s'} ->
  {s' | |_ s, h _| -- sra rd rt sa; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //.
eapply while.exec_seq; [by apply while.exec_cmd0, exec0_sra | exact H].
Qed.

Lemma exists_srl_seq_P rd rt sa c s h P :
  {s' | |_ store.upd rd ([rt]_s `>> '|u2Z sa|) s, h _| -- c ---> s' /\ P s'} ->
  {s' | |_ s, h _| -- srl rd rt sa; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //.
eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_or_seq_P rd rs rt c s h P :
  {s' | Some (store.upd rd ([rs]_s `|` [rt]_s) s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- cmd_or rd rs rt; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //.
eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_seq c1 c2 s :
  (exists si, s -- c1  ---> si /\ exists s', si -- c2  ---> s') ->
  (exists s' , s -- c1 ; c2 ---> s').
Proof. move=> [si [H1 [s' H2]]]. exists s'; by apply while.exec_seq with si. Qed.

Lemma exists_seq_P c1 c2 s (P : state -> Prop) Q :
  {si | Some s -- c1  ---> si /\ Q si} ->
  (forall si, Q si -> {s' | (si -- c2  ---> s') /\ forall st, s' = Some st -> P st}) ->
  {s' | Some s -- c1 ; c2 ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> [si [Hc1 Hsi]] Hc2.
case: {Hc2}(Hc2 _ Hsi) => sf [Hc2 HPsf].
exists sf; split; [by eapply while.exec_seq; eauto | exact HPsf].
Qed.

Lemma exists_seq_P2 c1 c2 s (Q : state -> Prop) :
  {si | Some s -- c1  ---> si /\ forall st, si = Some st -> Q st} ->
  (forall si, Q si -> {s' | Some si -- c2  ---> s' }) ->
  {s' | Some s -- c1 ; c2 ---> s' }.
Proof.
move=> [si [Hc1 Hsi]] Hc2.
destruct si as [si|].
- move: {Hsi}(Hsi _ (refl_equal _)) => Hsi.
  case: {Hc2}(Hc2 _ Hsi) => s' Hc2; exists s'. by eapply while.exec_seq; eauto.
- exists None.
  move/while.exec_seq : Hc1; apply. by apply while.exec_none.
Qed.

Lemma exists_ifte s (c1 c2 : while.cmd) bt :
  { s' | Some s -- c1 ---> s' } -> { s' | Some s -- c2 ---> s' } ->
  { s' | Some s -- If bt Then c1 Else c2 ---> s' }.
Proof.
move=> [s'1 H1] [s'2 H2].
apply constructive_indefinite_description.
case/boolP : (eval_b bt (fst s)) => Hbt.
- exists s'1; by apply while.exec_ifte_true.
- exists s'2; apply while.exec_ifte_false => //; by apply/negP.
Qed.

Lemma exists_ifte_P s (c1 c2 : while.cmd) bt (P : state -> Prop) :
  { s' | Some s -- c1 ---> s' /\ forall st, s' = Some st -> P st } ->
  { s' | Some s -- c2 ---> s' /\ forall st, s' = Some st -> P st } ->
  { s' | Some s -- If bt Then c1 Else c2 ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> [s'1 [H1 HP1]] [s'2 [H2 HP2]].
apply constructive_indefinite_description.
case/boolP : (eval_b bt (fst s)) => Hbt.
- exists s'1; split => //; by apply while.exec_ifte_true.
- exists s'2; split => //; apply while.exec_ifte_false => //; by apply/negP.
Qed.

Lemma exists_multu_seq rs rt c s h :
  {s' | Some (store.multu_op ([rs]_s `* [rt]_s) s, h) -- c ---> s' } ->
  {s' | Some (s, h) -- multu rs rt ; c ---> s' }.
Proof.
move=> [s' H].
exists s'; eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_multu_seq_P rs rt c s h P :
  {s' | Some (store.multu_op ([rs]_s `* [rt]_s) s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- multu rs rt ; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_maddu_seq_P rs rt c s h P :
  {s' | Some (store.maddu_op ([rs]_s `* [rt]_s) s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- maddu rs rt ; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_mflo_P rd s h (P : _ -> Prop) :
  P (Some (store.upd rd (store.lo s) s, h)) ->
  {s' | Some (s, h) -- mflo rd  ---> s' /\ P s' }.
Proof.
eexists; split.
by do 2 constructor.
done.
Qed.

Lemma exists_mflo_seq_P rd c s h P :
  {s' | Some (store.upd rd (store.lo s) s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- mflo rd ; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto. do 2 constructor.
Qed.

Lemma exists_mfhi_seq_P rd c s h P :
  {s' | Some (store.upd rd (store.hi s) s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- mfhi rd ; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_mtlo_seq_P rs c s h P :
  {s' | Some (store.mtlo_op [rs]_s s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- mtlo rs ; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_mflhxu_P rd s h (P : state -> Prop) :
  P (store.mflhxu_op (store.upd rd (store.lo s) s), h) ->
  {s' | Some (s, h) -- mflhxu rd ---> s' /\ forall st, s' = Some st -> P st}.
Proof.
move=> H.
exists (Some (store.mflhxu_op (store.upd rd (store.lo s) s), h)); split => //.
do 2 constructor.
by move=> st [] <-.
Qed.

Lemma exists_addu_seq_P rd rs rt c s h P :
  {s' | Some (store.upd rd ([rs]_s `+ [rt]_s) s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- addu rd rs rt ; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto; do 2 constructor.
Qed.

Lemma exists_sltu_seq_P rd rs rt c s h P flag :
  flag = (if Zlt_bool (u2Z [rs]_s) (u2Z [rt]_s) then one32 else zero32) ->
  {s' | Some (store.upd rd flag s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- sltu rd rs rt ; c ---> s' /\ P s' }.
Proof.
move=> Hflag [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto. do 2 constructor => //.
Qed.

Lemma exists_msubu_seq_P rs rt c s h P :
  {s' | Some (store.msubu_op ([rs]_s `* [rt]_s) s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- msubu rs rt; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto. do 2 constructor.
Qed.

Lemma exists_movz_true_seq_P rd rs rt c s h P : [ rt ]_s = zero32 ->
 {s' | Some (store.upd rd [rs]_s s, h) -- c ---> s' /\ P s'} ->
 {s' | Some (s, h) -- movz rd rs rt; c ---> s' /\ P s' }.
Proof.
move=> Hrt [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto; by do 2 constructor.
Qed.

Lemma exists_movz_false_seq_P rd rs rt c s h P : [ rt ]_s <> zero32 ->
 {s' | Some (s, h) -- c ---> s' /\ P s'} ->
 {s' | Some (s, h) -- movz rd rs rt; c ---> s' /\ P s' }.
Proof.
move=> Hrt [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto; by do 2 constructor.
Qed.

Lemma exists_movz_true_P rd rs rt s h (P : state -> Prop) :
 [rt]_s = zero32 ->
 P (store.upd rd [rs]_s s, h) ->
 {s' | Some (s, h) -- movz rd rs rt ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> Hrt HP.
eapply exist; split => //.
do 2 constructor => //.
by move=> st [] <-.
Qed.

Lemma exists_movz_false_P rd rs rt s h (P : state -> Prop) :
 [rt]_s <> zero32 -> P (s, h) ->
 {s' | Some (s, h) -- movz rd rs rt ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> Hrt HP.
eapply exist; split => //.
constructor.
apply exec0_movz_false => //.
by move=> st [] <-.
Qed.

Lemma exists_movn_true_seq_P rd rs rt c s h P :
  [rt]_s <> zero32 ->
  {s' | Some (store.upd rd [rs]_s s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- movn rd rs rt; c ---> s' /\ P s' }.
Proof.
move=> Hrt [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto; by do 2 constructor.
Qed.

Lemma exists_movn_false_seq_P rd rs rt c s h P : [ rt ]_s = zero32 ->
  {s' | Some (s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- movn rd rs rt; c ---> s' /\ P s' }.
Proof.
move=> Hrt [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto; do 2 constructor => //.
Qed.

Lemma exists_movn_true_P rd rs rt s h (P : state -> Prop) :
  [rt]_s <> zero32 -> P (store.upd rd [rs]_s s, h) ->
  {s' | Some (s, h) -- movn rd rs rt ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> Hrt HP.
eapply exist; split => //.
do 2 constructor => //.
by move=> st [] <-.
Qed.

Lemma exists_movn_false_P rd rs rt s h (P : state -> Prop) :
  [rt]_s = zero32 -> P (s, h) ->
  {s' | Some (s, h) -- movn rd rs rt ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> Hrt HP.
eapply exist; split => //.
constructor.
apply exec0_movn_false => //.
by move=> st [] <-.
Qed.

Lemma exists_xori_seq_P rt rs (imm : int 16) c s h P :
  {s' | Some (store.upd rt ([rs]_s `(+) zext 16 imm) s, h) -- c ---> s' /\ P s'} ->
  {s' | Some (s, h) -- xori rt rs imm; c ---> s' /\ P s' }.
Proof.
move=> [s' [H HP]].
exists s'; split => //.
eapply while.exec_seq; eauto; by do 2 constructor.
Qed.

Lemma exists_subu_seq_P rd rs rt c s h P :
  {s' | Some (store.upd rd ([rs]_s `+ (cplt2 [rt]_s))%mips_expr s, h) -- c ---> s' /\ P s'}%mips_cmd ->
  {s' | Some (s, h) -- subu rd rs rt ; c ---> s' /\ P s' }%mips_cmd.
Proof.
move=> [s' [H HP]].
exists s'; split => //; eapply while.exec_seq; eauto.
by do 2 constructor.
Qed.

Lemma exists_sw rt (off : int 16) base s h :
  {s' | Some (s, h) -- sw rt off base ---> s' }%mips_cmd.
Proof.
apply constructive_indefinite_description.
case: (classic (exists l , u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat l /\ exists z, heap.get l h = Some z))%mips_expr => X.
- case:X => l0 [Hl0 [z Hz]].
  eexists.
  do 2 constructor.
  by apply Hl0.
  by exists z.
- exists None.
  constructor.
  by apply exec0_sw_err.
Qed.

Lemma exists_sw_P rt (off : int 16) base s h p (P : state -> Prop) :
  u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat p ->
  P (s, heap.upd p ([rt]_s) h) ->
  {s' | Some (s, h) -- sw rt off base ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> Hp HP.
apply constructive_indefinite_description.
case: (classic (exists z, heap.get p h = Some z)) => X.
apply constructive_indefinite_description'.
eapply exist.
split.
by apply while.exec_cmd0, (exec0_sw _ _ _ _ _ _ Hp X).
by move=> st [] <-.
exists None; split => //.
do 2 constructor.
contradict X.
case: X => l [H1 H2].
suff : p = l by move=> ->.
lia.
Qed.

Lemma exists_sw_seq rt (off : int 16) base c s h p :
  u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat p ->
  {s' | Some (s, heap.upd p [rt]_s h) -- c ---> s' } ->
  {s' | Some (s, h) -- sw rt off base; c ---> s' }.
Proof.
move=> Hp [s' H].
apply constructive_indefinite_description.
case: (classic (exists l , u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat l /\ exists z, heap.get l h = Some z)) => X.
- case:X => l0 [Hl0 [z Hz]].
  exists s'; eapply while.exec_seq; eauto; do 2 constructor.
  lia.
  exists z => //.
  suff : p = l0 by move=> ->.
  lia.
- exists None.
  eapply while.exec_seq.
  constructor.
  apply exec0_sw_err => //.
  by apply while.exec_none.
Qed.

Lemma exists_sw_seq_P rt (off : int 16) base c s h p (P : state -> Prop) :
  u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat p ->
  {s' | Some (s, heap.upd p [rt]_s h) -- c ---> s' /\ forall st, s' = Some st -> P st } ->
  {s' | Some (s, h) -- sw rt off base; c ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> Hp [s' [H HP]].
apply constructive_indefinite_description.
case: (classic (exists l, u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat l /\ exists z, heap.get l h = Some z)) => X.
- case:X => l0 [Hl0 [z Hz]].
  exists s'; split => //; eapply while.exec_seq; eauto; do 2 constructor.
  lia.
  exists z => //.
  suff : p = l0 by move=> ->.
  lia.
- exists None; split => //.
  eapply while.exec_seq.
  constructor.
  apply exec0_sw_err => //.
  by apply while.exec_none.
Qed.

Lemma exists_lw_seq_P rt (off : int 16) base c s h p z (P : state -> Prop) :
  u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat p ->
  heap.get p h = Some z ->
  {s' | Some (store.upd rt z s, h) -- c ---> s' /\ forall st, s' = Some st -> P st } ->
  {s' | Some (s, h) -- lw rt off base ; c ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> Hp Hz [s' [H HP]].
apply constructive_indefinite_description.
case: (classic (exists l, u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat l /\ exists z, heap.get l h = Some z)) => X.
- case:X => l0 [Hl0 [z0 Hz0]].
  have X : p = l0 by lia.
  subst l0.
  have X : z = z0 by rewrite Hz in Hz0; case: Hz0 => //.
  subst z0.
  exists s'; split => //.
  eapply while.exec_seq; eauto.
  by apply while.exec_cmd0, (exec0_lw _ _ _ _ _ _ _ Hp).
- exists None; split => //.
  eapply while.exec_seq.
  constructor.
  apply exec0_lw_error => //.
  by apply while.exec_none.
Qed.

Lemma exists_lwxs_seq_P rt idx base c s h p z (P : state -> Prop) :
  u2Z ([base]_s `+ ([idx]_s `<< 2)) = 4 * Z_of_nat p ->
  heap.get p h = Some z ->
  {s' | Some (store.upd rt z s, h) -- c ---> s' /\ forall st, s' = Some st -> P st } ->
  {s' | Some (s, h) -- lwxs rt idx base; c ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> Hp Hz [s' [H HP]].
apply constructive_indefinite_description.
case: (classic (exists l, u2Z ([base]_s `+ ([idx]_s `<< 2)) = 4 * Z_of_nat l /\ exists z, heap.get l h = Some z)) => X.
- case:X => l0 [Hl0 [z0 Hz0]].
  have X : p = l0 by lia.
  subst l0.
  have X : z = z0 by rewrite Hz in Hz0; case: Hz0 => //.
  subst z0.
  exists s'; split => //.
  eapply while.exec_seq; eauto.
  by apply while.exec_cmd0, (exec0_lwxs _ _ _ _ _ _ _ Hp).
- exists None; split => //.
  eapply while.exec_seq; by [apply while.exec_cmd0, exec0_lwxs_error | apply while.exec_none].
Qed.

Lemma exists_while s h (c : while.cmd) bt : eval_b bt s ->
  { s' | Some (s, h) -- c ; While bt {{ c }} ---> s'} ->
  { s' | Some (s, h) -- While bt {{ c }} ---> s'}.
Proof.
move=> Heval_b [s' H]; exists s'; by apply semop_prop_m.while_seq'.
Qed.

Lemma exists_while_P s h (c : while.cmd) bt (P : state -> Prop) :
  eval_b bt s ->
  { s' | Some (s, h) -- c ; While bt {{ c }} ---> s' /\ forall st, s' = Some st -> P st } ->
  { s' | Some (s, h) -- While bt {{ c }} ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> Heval_b [s' [H HP]].
exists s'; split; [by apply semop_prop_m.while_seq' | exact HP ].
Qed.

Lemma exists_while_false s h (c : while.cmd) bt : ~~ eval_b bt s -> 
  { s' | Some (s, h) -- While bt {{ c }} ---> s' }.
Proof.
move=> Heval_b.
exists (Some (s, h)); by apply while.exec_while_false.
Qed.

Lemma exists_while_false_P s h (c : while.cmd) bt (P : state -> Prop) :
  ~~ eval_b bt s -> P (s, h) ->
  { s' | Some (s, h) -- While bt {{ c }} ---> s' /\ forall st, s' = Some st -> P st }.
Proof.
move=> Heval_b HP.
exists (Some (s, h)); split; by [apply while.exec_while_false | move=> st [<-]].
Qed.

Ltac exists_sw1_classic l_idx H_l_idx z_idx H_z_idx X :=
  match goal with
    | |- @ex _ (fun _ => ((Some (?s, ?h) -- (cmd_cmd0_coercion (sw ?rt ?off ?base)) ---> _) /\ _)) => 
      let K := fresh in 
      assert (K : Decidable.decidable 
        (exists l, u2Z ( [base]_ s `+ sext 16 off) = 4 * Z_of_nat l /\ 
         exists v, heap.get l h = Some v) ); 
        [
         by apply Classical_Prop.classic |
         case: K => [ [l_idx [H_l_idx [z_idx H_z_idx] ] ] | X ]
        ]
  end.

Ltac exists_sw1 l_idx H_l_idx z_idx H_z_idx :=
  match goal with
    | |- @sig _ (fun _ => ((Some (?s, ?h) -- (cmd_cmd0_coercion (sw ?rt ?off ?base)) ---> _)%mips_cmd /\ _)) => 
      apply Epsilon.constructive_indefinite_description ;
      let X := fresh in 
      exists_sw1_classic l_idx H_l_idx z_idx H_z_idx X ;
      [ (apply constructive_indefinite_description' ;
        apply exists_sw_P with l_idx ;  [assumption | idtac ])
      |  
        (exists None; split; 
         [ (constructor ; by apply exec0_sw_err)
         | done
         ])
      ]
  end.

Ltac exists_sw_classic_new l_idx H_l_idx z_idx H_z_idx X :=
  match goal with
    | |- @ex _ (fun _ => (Some (?s, ?h) -- (cmd_cmd0_coercion (sw ?rt ?off ?base) ; _) ---> _)) => 
       let K := fresh in 
       assert (K : Decidable.decidable 
         (exists l, u2Z ([base]_ s `+ sext 16 off) = 4 * Z_of_nat l /\ 
           exists v, heap.get l h = Some v) ) ;
         [
         by apply Classical_Prop.classic
         |
         case: K => [ [l_idx [H_l_idx [z_idx H_z_idx] ] ] | X ]
         ]
  end.

(* TODO: rename *)
Ltac exists_sw_new l_idx H_l_idx z_idx H_z_idx :=
  match goal with
    | |- @sig _ (fun _ => (Some (?s, ?h) -- (cmd_cmd0_coercion (sw ?rt ?off ?base) ; _) ---> _)) => 
      apply Epsilon.constructive_indefinite_description ;
      let X := fresh in 
      exists_sw_classic_new l_idx H_l_idx z_idx H_z_idx X;
      [
        (apply constructive_indefinite_description' ;
          apply exists_sw_seq with l_idx ; [assumption | idtac] )
        |  
          (exists None ;
           eapply while.exec_seq ;
           constructor => // ;
           apply exec0_sw_err => // ;
           apply while.exec_none )
      ]
  end.

Ltac exists_sw_P_classic l_idx H_l_idx z_idx H_z_idx X :=
  match goal with
    | |- @ex _ (fun _ => ((Some (?s, ?h) -- (cmd_cmd0_coercion (sw ?rt ?off ?base) ; _) ---> _) /\ _)) => 
      let K := fresh in 
      assert (K : Decidable.decidable 
        (exists l, u2Z (([base]_ s) `+ sext 16 off) = 4 * Z_of_nat l /\ 
          exists v, heap.get l h = Some v) ) ;
        [by apply Classical_Prop.classic
        |
        case: K => [ [l_idx [H_l_idx [z_idx H_z_idx] ] ] | X ]
        ]
  end.

Ltac exists_sw_P l_idx H_l_idx z_idx H_z_idx :=
  match goal with
    | |- @sig _ (fun _ => ((Some (?s, ?h) -- (cmd_cmd0_coercion (sw ?rt ?off ?base) ; _) ---> _) /\ _)) => 
      apply Epsilon.constructive_indefinite_description ;
      let X := fresh in 
      exists_sw_P_classic l_idx H_l_idx z_idx H_z_idx X ;
      [ (apply constructive_indefinite_description' ;
          apply exists_sw_seq_P with l_idx ; [assumption | idtac] )
        |  
         (exists None ;
          split => // ;
          eapply while.exec_seq ;
          constructor => // ;
          apply exec0_sw_err => // ;
          apply while.exec_none )
      ]
  end.

Ltac exists_lwxs_classic location Hlocation value Hvalue X :=
  match goal with
    | |- @ex _ (fun _ => ((Some (?s, ?h) -- (cmd_cmd0_coercion (lwxs ?rt ?idx ?base) ; _) ---> _)%mips_cmd /\ _)) => 
      let K := fresh in 
      assert (K : Decidable.decidable 
        (exists p, u2Z (([base]_ s)%mips_expr `+ ([idx]_s `<< 2)) = 4 * Z_of_nat p /\ 
        exists v, heap.get p h = Some v)%mips_expr) ;
       [by apply Classical_Prop.classic |
        case : K => 
        [ [location [Hlocation [value Hvalue] ] ] | X ] ]
  end.

Ltac exists_lwxs location Hlocation value Hvalue :=
  match goal with
    | |- @sig _ (fun _ => ((Some (?s, ?h)) -- (cmd_cmd0_coercion (lwxs ?rt ?idx ?base) ; _) ---> _)%mips_cmd /\ _) =>
      apply Epsilon.constructive_indefinite_description ;
      let X := fresh in
      exists_lwxs_classic location Hlocation value Hvalue X ;
      [ (apply constructive_indefinite_description' ;
         apply exists_lwxs_seq_P with location value; [assumption | assumption | idtac ])
      | (apply constructive_indefinite_description' ;
         exists None; split ; [
         apply while.exec_seq with None ;
         [ (apply while.exec_cmd0 ;
            by apply exec0_lwxs_error)
         |
            by apply while.exec_none
         ] | done ])
      ]
  end.

Ltac exists_lw_classic location Hlocation value Hvalue X :=
  match goal with
    | |- @ex _ (fun _ => ((Some (?s, ?h) -- (cmd_cmd0_coercion (lw ?rt ?off ?base) ; _) ---> _)%mips_cmd /\ _)) => 
    let K := fresh in
       assert (K : 
         Decidable.decidable 
         (exists p, u2Z (([base]_ s)%mips_expr `+ sext 16 off) = 4 * Z_of_nat p /\ 
         exists v, heap.get p h = Some v)%mips_expr ) ;
       [ by apply Classical_Prop.classic |
         case: K => [ [location [Hlocation [value Hvalue] ] ] | X ]
         ]
  end.

Ltac exists_lw location Hlocation value Hvalue :=
  match goal with
    | |- @sig _ (fun _ => ((Some (?s, ?h)) -- (cmd_cmd0_coercion (lw ?rt ?off ?base) ; _) ---> _)%mips_cmd /\ _) =>
      apply Epsilon.constructive_indefinite_description ;
      let X := fresh in
      exists_lw_classic location Hlocation value Hvalue X ;
      [ (apply constructive_indefinite_description' ;
         apply exists_lw_seq_P with location value => //)
      | (apply constructive_indefinite_description' ;
         exists None; split => // ;
         apply while.exec_seq with None ;
         [ (apply while.exec_cmd0 ;
            by apply exec0_lw_error)
         |
            by apply while.exec_none
         ])
      ]
  end.

Ltac exists_movn H :=
  match goal with
    | |- @sig _ (fun _ => ((Some (?s, ?h) -- (cmd_cmd0_coercion (movn ?rd ?rs ?rt) ; _) ---> _)%mips_cmd /\ _)) =>
      case: (dec_int ([rt]_(s))
        zero32) => H
  end.

Ltac exists_movz1 H :=
  match goal with
    | |- @sig _ (fun _ => ((Some (?s, ?h) -- (cmd_cmd0_coercion (movz ?rd ?rs ?rt)) ---> _)%mips_cmd /\ _)) =>
      case: (dec_int ([rt]_(s))
        zero32) => H
  end.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext.
Require Import machine_int.
Import MachineInt.
Require Import mips_cmd.
Export mips_cmd.

Declare Scope mips_hoare_scope.

Local Close Scope positive_scope.
Local Open Scope heap_scope.
Import expr_m.
Local Open Scope mips_expr_scope.
Import assert_m.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope machine_int_scope.

(** * Separation Logic *)

(** Predicate transformers *)

Local Open Scope zarith_ext_scope.

(** The effect of executing %\coqdocvar{add rd rs rt}%#add rd rs rt# is
to update the contents of the register %\coqdocvar{rd}%#rd# with the result of the
operation %\coqdocvar{vrs}\ensuremath{\boxplus}\coqdocvar{vrt}%#vrs `+ vrt# (where %vrs%#vrs# and %vrt%#vrt# are the contents of the registers rs and rt), provided the addition in
two's complement does not overflow: *)
Definition wp_add rd rs rt P : assert := fun s h =>
  - 2 ^^ 31 <=  s2Z [rs]_s + s2Z [rt]_s < 2 ^^ 31 /\
  P (store.upd rd ([rs]_s `+ [rt]_s) s) h.

Definition wp_addi rt rs (imm : immediate) P : assert := fun s h =>
  - 2 ^^ 31 <= s2Z ([rs]_s) + s2Z (sext 16 imm) < 2 ^^ 31 /\
  P (store.upd rt ([rs]_s `+ sext 16 imm) s) h.

Definition wp_addiu rt rs (imm : immediate) P : assert := fun s =>
  P (store.upd rt ([rs]_s `+ sext 16 imm) s).

Definition wp_addu rd rs rt P : assert := fun s =>
  P (store.upd rd ([rs]_s `+ [rt]_s) s).

Definition wp_and rd rs rt P : assert := fun s =>
  P (store.upd rd ([rs]_s `& [rt]_s) s).

Definition wp_andi rt rs (imm : immediate) P : assert := fun s =>
  P (store.upd rt ([rs]_s `& zext 16 imm) s).

(** The function wp_lw checks that the access is word-aligned and the cell-contents
specified: *)
Definition wp_lw rt (off : immediate) base P : assert := fun s h =>
 exists p, u2Z (eval (var_e base) s `+ sext 16 off) = 4 * Z_of_nat p /\
  exists z, heap.get p h = Some z /\ P (store.upd rt z s) h.

Definition wp_lwxs rt idx base P : assert := fun s h =>
 exists l, u2Z ([base]_s `+ shl 2 [idx]_s) = 4 * Z_of_nat l /\
  exists z, heap.get l h = Some z /\ P (store.upd rt z s) h.

Definition wp_maddu rs rt P : assert := fun s h =>
  P (store.maddu_op ([rs]_s `* [rt]_s) s) h .

Definition wp_mfhi rd P : assert := fun s h =>
  P (store.upd rd (store.hi s) s) h.

Definition wp_mflhxu rd P : assert := fun s h =>
  P (store.mflhxu_op (store.upd rd (store.lo s) s)) h.

Definition wp_mflo rd P : assert := fun s h =>
  P (store.upd rd (store.lo s) s) h.

Definition wp_movn rd rs rt (P : assert) : assert := fun s h =>
  ([rt]_s <> zero32 -> P (store.upd rd [rs]_s s) h) /\
  ([rt]_s = zero32 -> P s h).

Definition wp_movz rd rs rt (P : assert) : assert := fun s h =>
  ([rt]_s = zero32 -> P (store.upd rd [rs]_s s) h) /\
  ([rt]_s <> zero32 -> P s h).

Definition wp_msubu rs rt P : assert := fun s h =>
  P (store.msubu_op ([rs]_s `* [rt]_s) s) h.

Definition wp_mthi rs P : assert := fun s h =>
  P (store.mthi_op [rs]_s s) h.

Definition wp_mtlo rs P : assert := fun s h =>
  P (store.mtlo_op [rs]_s s) h.

Definition wp_multu rs rt P : assert := fun s h =>
  P (store.multu_op ([rs]_s `* [rt]_s) s) h.

Definition wp_nor rd rs rt P : assert := fun s =>
  P (store.upd rd (int_not (int_or [rs]_s [rt]_s)) s).

Definition wp_or rd rs rt P : assert := fun s =>
  P (store.upd rd (int_or [rs]_s [rt]_s) s).

Definition wp_sll rx ry (sa : shifta) P : assert := fun s =>
  P (store.upd rx (shl '|u2Z sa| [ry]_s) s).

Definition wp_sllv rd rt rs P : assert := fun s =>
  P (store.upd rd ([rt]_s `<< '| u2Z ([rs]_s `% 5)|) s).

Definition wp_sltu rd rs rt P : assert := fun s =>
  P (store.upd rd (if (u2Z [rs]_s <? u2Z [rt]_s) then one32 else zero32) s).

Definition wp_sra rd rt (sa : shifta) P : assert := fun s =>
  P (store.upd rd (shra '|u2Z sa| [rt]_s) s).

Definition wp_srl rd rt (sa : shifta) P : assert := fun s =>
  P (store.upd rd ([rt]_s `>> '|u2Z sa|) s).

Definition wp_srlv rd rt rs P : assert := fun s =>
  P (store.upd rd ([rt]_s `>> '|u2Z ([rs]_s `% 5)|) s).

Definition wp_subu rd rs rt P : assert := fun s =>
  P (store.upd rd ([rs]_s `+ cplt2 [rt]_s) s).

Definition wp_sw rt (off : immediate) base P : assert := fun s h =>
  exists l, u2Z ([base]_s `+ sext 16 off) = 4 * Z_of_nat l /\
    (exists z, heap.get l h = Some z) /\
    P s (heap.upd l [rt]_s h).

Definition wp_xor rd rs rt P : assert := fun s =>
  P (store.upd rd (int_xor [rs]_s [rt]_s) s).

Definition wp_xori rt rs imm P : assert := fun s =>
  P (store.upd rt (int_xor [rs]_s (zext 16 imm)) s).

Definition wp0 (c : cmd0) (Q : assert) : assert :=
match c with
  | nop => Q
  | add rd rs rt => wp_add rd rs rt Q
  | addi rt rs imm => wp_addi rt rs imm Q
  | addiu rt rs imm => wp_addiu rt rs imm Q
  | addu rd rs rt => wp_addu rd rs rt Q
  | cmd_and rd rs rt => wp_and rd rs rt Q
  | andi rt rs imm => wp_andi rt rs imm Q
  | lw rt offset base => wp_lw rt offset base Q
  | lwxs rt index base => wp_lwxs rt index base Q
  | maddu rs rt => wp_maddu rs rt Q
  | mfhi rd => wp_mfhi rd Q
  | mflhxu rd  => wp_mflhxu rd Q
  | mflo rd => wp_mflo rd Q
  | movn rd rs rt => wp_movn rd rs rt Q
  | movz rd rs rt => wp_movz rd rs rt Q
  | mthi rs => wp_mthi rs Q
  | mtlo rs => wp_mtlo rs Q
  | msubu rs rt => wp_msubu rs rt Q
  | multu rs rt => wp_multu rs rt Q
  | nor rd rs rt => wp_nor rd rs rt Q
  | cmd_or rd rs rt => wp_or rd rs rt Q
  | sll rx ry sa => wp_sll rx ry sa Q
  | sllv rd rs rt => wp_sllv rd rs rt Q
  | sltu rd rs rt => wp_sltu rd rs rt Q
  | sra rd rt sa => wp_sra rd rt sa Q
  | srl rd rt sa => wp_srl rd rt sa Q
  | srlv rd rt rs => wp_srlv rd rt rs Q
  | subu rd rs rt => wp_subu rd rs rt Q
  | sw rt offset base => wp_sw rt offset base Q
  | xor rd rs rt => wp_xor rd rs rt Q
  | xori rt rs imm => wp_xori rt rs imm Q
end.

Lemma wp0_no_err : forall s h c P,
  wp0 c P s h -> ~ (Some (s,h) -- c ----> None).
Proof.
move=> s h c P Hwp0 Hexec; inversion Hexec as [ | |
(* addi_err *)s' h' rt rs imm Hcond Hs Hc HNone | |
(* add_err *)s' h' rt rs imm Hcond Hs Hc HNone | | | | | |
(* lw_err *)s' h' rt off base Hcond | |
(* lwxs_err *)s' h' rt off base Hcond | | | | | | | | | | | | | | | | | | | | | | |
(* sw_err *)s' h' rt off base Hcond | | ]; subst.
- by case: Hwp0 => Hwp0 _ //.
- by case: Hwp0 => Hwp0 _ //.
- case: Hwp0 => x [Hx [z [Hz _]]].
  rewrite [eval _ _]/= in Hx.
  by apply Hcond; exists x; split => //; exists z.
- case: Hwp0 => x [Hx [z [Hz _]]].
  by apply Hcond; exists x; split => //; exists z.
- case: Hwp0 => x [Hx [[z Hz] _]].
  by apply Hcond; exists x; split => //; exists z.
Qed.

Lemma exec0_from_wp0 : forall ST (c : cmd0) ST', ST -- c ----> ST' ->
  forall P s h s' h', ST = Some (s, h) -> ST' = Some (s', h') ->
    wp0 c P s h -> P s' h'.
Proof.
move=> ST c ST'; elim => //; clear ST c ST'.
- (* nop *) by move=> st P s h0 s' h' -> [] <- <- ?.
- move=> s h rd rs rt H P s1 h1 s' h' [] X Y; subst.
  case=> X Y; subst; rewrite /= /wp_add; tauto.
- move=> s h rt rs imm H P s1 h1 s' h' [] X Y; subst.
  case=> X Y; subst; rewrite /= /wp_addi; tauto.
- (* addiu *) by move=> s h rd rs rt P s1 h1 s' h' [] <- <- [] <- <-.
- (* addu *) by move=> s h rt rs imm P s1 h1 s' h' [] <- <- [] <- <-.
- (* cmd_and *) by move=> s h rd rs rt P s1 h1 s' h' [] <- <- [] <- <-.
- (* andi *) by move=> s h rt rs imm P s1 h1 s' h' [] <- <- [] <- <-.
- (* lw *) move=> s h rt offst base p z Hp Hz P s0 h0 s' h' [] X Y; subst.
  case=> X Y; subst; case=> p' [Hp' [z' [Hz' HP]]].
suff : z = z' by move=> ->.
  have X : p = p' by rewrite [eval _ _]/= in Hp'; by omega.
  subst; rewrite Hz' in Hz; by case: Hz.
- (* lwxs *) move=> s h rt index base p z Hp Hz P s0 eh0 s' h' [] X Y; subst.
  case=> X Y; subst; case=> p' [Hp' [z' [Hz' HP]]].
  suff : z = z' by move=> ->.
  have X : p = p' by omega.
  subst; rewrite Hz' in Hz; by case: Hz.
- (* maddu *) by move=> s h rs rt P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* mfhi *) by move=> s h rd P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* mflhxu *) by move=> s h rd P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* mflo *) by move=> s h rd P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* movn true *) move=> s h rd rs rt H P s0  h0 s1 h1 [] X Y; subst.
  case=> X Y; subst; rewrite /= /wp_movn; tauto.
- (* movn false *) move=> s h rd rs rt H P s0 h0 s1 h1 [] X Y; subst.
  case=> X Y; subst; rewrite /= /wp_movn; tauto.
- (* movz true *) move=> s h rd rs rt H P s0 h0 s1 h1 [] X Y; subst.
  case=> X Y; subst; rewrite /= /wp_movz; tauto.
- (* movz false *) move=> s h rd rs rt H P s0 h0 s1 h1 [] X Y; subst.
  case=> X Y; subst; rewrite /= /wp_movz; tauto.
- (* msubu *) by move=> s h rs rt P s1 h1 s' h' [] <- <- [] <- <-.
- (* mthi *) by move=> s h rs P s1 h1 s' h' [] <- <- [] <- <-.
- (* mtlo *) by move=> s h rs P s1 h1 s' h' [] <- <- [] <- <-.
- (* multu *) by move=> s h rs rt P s1 h1 s' h' [] <- <- [] <- <-.
- (* no *) by move=> s h rd rs rt P s1 h1 s' h' [] <- <- [] <- <-.
- (* cmd_or *) by move=> s h rd rs rt P s1 h1 s' h' [] <- <- [] <- <-.
- (* sll *) by move=> s h rx ry sa P s0 h0 s' h' [] <- <- [] <- <-.
- (* sllv *) by move=> s h rd rs rt P s0 h0 s' h' [] <- <- [] <- <-.
- (* sltu *) move=> s h rd rs rt flag H P s0 h0 s1 h1 [] X Y; subst.
  case=> X Y; subst => //.
- (* sra *) by move=> s h rd rt sa P s0 h0 s' h' [] <- <- [] <- <-.
- (* srl *) by move=> s h rd rt sa P s0 h0 s' h' [] <- <- [] <- <-.
- (* srlv *) by move=> s h rd rt rs P s0 h0 s' h' [] <- <- [] <- <-.
- (* subu *) by move=> s h rd rs rt P s1 h1 s' h' [] <- <- [] <- <-.
- (* sw *) move => s h rt off base p H [z Hz] P s1 h1 s' h' [] X Y; subst.
  case=> X Y; subst; case=> l [Hl [z' Hz']].
  suff : p = l by move=> ->.
  omega.
- (* xor *) by move=> s h rd rs rt P s1 h1 s' h' [] <- <- [] <- <-.
- (* xori *) by move=> s h rt rs imm P s1 h1 s' h' [] <- <- [] <- <-.
Qed.

Lemma exec0_to_wp0 : forall ST (c : cmd0) ST', ST -- c ----> ST' ->
  forall (P: assert) s h s' h', ST = Some (s,h) -> ST' = Some (s',h') ->
    P s' h' -> wp0 c P s h.
Proof.
move=> ST c ST'; elim => //; clear ST c ST'.
- (* nop *) by move=> st P s h s' h' -> [] <- <- ?.
- (* add *) by move=> s h rd rs rt H P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* addi *) by move=> s h rt rs imm H P s1 h2 s' h' [] <- <- [] <- <-.
- (* addiu *) by move=> s h rt rs imm P s1 h2 s' h' [] <- <- [] <- <-.
- (* addu *) by move=> s h rd rs rt P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* cmd_and *) by move=> s h rd rs rt P s0 h0 s' h' [] <- <- [] <- <-.
- (* andi *) by move=> s h rt rs imm P s0 h0 s' h' [] <- <- [] <- <-.
- (* lw *) move=> s h rt offset base p z H Hz P s0 h0 s1 h1 [] X Y; subst.
  case=> X Y; subst; rewrite /wp0 /wp_lw // => H'.
  by exists p; split => //; exists z => //.
- (* lwxs *) move=> s h rt index base p z Hp Hz P s0 h0 s1 h1 [] X Y; subst.
  case=> X Y; subst; rewrite /= /wp0 /wp_lwxs => H'.
  by exists p; split => //; exists z => //.
- (* maddu *) by move=> s h rs rt P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* mfhi *) by move=> s h rd P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* mflhxu *) by move=> s h rd P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* mflo *) by move=> s h rd P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* movn true *) by move=> s h rd rs rt H P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* movn false *) by move=> s h rd rs rt H P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* movz true *) by move=> s h rd rs rt H P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* movz false *) by move=> s h rd rs rt H P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* msubu *) by move=> s h rs rt P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* mthi *) by move=> s h rs P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* mtlo *) by move=> s h rs P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* multu *) by move=> s h rs rt P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* nor *) by move=> s h rd rs rt P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* cmd_or *) by move=> s h rd rs rt P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* sll *) by move=> s h rd rt sa P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* sllv *) by move=> s h rd rs rt P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* sltu *) move=> s h rd rs rt flag Hflag P s0 h0 s1 h1 [] X Y; subst.
  case=> X Y; subst => //.
- (* sra *) by move=> s h rd rt sa P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* shrl *) by move=> s h rd rt sa P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* srlv *) by move=> s h rd rt rs P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* sw *) by move=> s h rd rs rt P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* subu *) move=> s h rt offset base p H [z Hz] P s1 h1 s' h' [] X Y; subst.
  case=> X Y; subst => H'.
  rewrite /wp0 /wp_sw.
  by exists p; split => //; split => //; exists z.
- (* xor *) by move=> s h rd rs rt P s0 h0 s1 h1 [] <- <- [] <- <-.
- (* xori *) by move=> s h rt rs imm P s0 h0 s1 h1 [] <- <- [] <- <-.
Qed.

Lemma exec0_wp0 : forall s h (c : cmd0) s' h', Some (s, h) -- c ----> Some (s', h') ->
  forall P, wp0 c P s h <-> P s' h'.
Proof.
move=> s h c s' h' H P; split=> H'.
eapply exec0_from_wp0; [by apply H | reflexivity | reflexivity | exact H'].
eapply exec0_to_wp0; [by apply H | reflexivity | reflexivity | exact H'].
Qed.

(* dummy *)
Notation "'_assert'" := assert : mips_hoare_scope.
Local Open Scope mips_hoare_scope.

(** Separation Logic (Partial Correctness) *)

(** Separation logic triples are formalized as an inductive relation
$\{ P \} c \{ Q \}$#{{ P }} c {{ Q }}# between commands and pre/post-conditions
encoded as assertions: *)
Reserved Notation "{{[ P ]}} c {{[ Q ]}}" (at level 82, no associativity).
Inductive hoare0 : assert -> cmd0 -> assert -> Prop :=
| hoare0_nop: forall P, {{[ P ]}} nop {{[ P ]}}
| hoare0_add: forall Q rs rt rd, {{[ wp_add rd rs rt Q ]}} add rd rs rt {{[ Q ]}}
| hoare0_addi : forall Q rt rs imm, {{[ wp_addi rt rs imm Q ]}} addi rt rs imm {{[ Q ]}}
| hoare0_addiu : forall Q rt rs imm, {{[ wp_addiu rt rs imm Q ]}} addiu rt rs imm {{[ Q ]}}
| hoare0_addu: forall Q rs rt rd , {{[ wp_addu rd rs rt Q ]}} addu rd rs rt {{[ Q ]}}
| hoare0_and : forall Q rd rs rt, {{[ wp_and rd rs rt Q ]}} cmd_and rd rs rt {{[ Q ]}}
| hoare0_andi : forall Q rt rs imm, {{[ wp_andi rt rs imm Q ]}} andi rt rs imm {{[ Q ]}}
| hoare0_lw : forall Q rt off base, {{[ wp_lw rt off base Q ]}} lw rt off base {{[ Q ]}}
| hoare0_lwxs : forall rt idx base Q, {{[ wp_lwxs rt idx base Q ]}} lwxs rt idx base {{[ Q ]}}
| hoare0_maddu : forall Q rs rt, {{[ wp_maddu rs rt Q ]}} maddu rs rt {{[ Q ]}}
| hoare0_mfhi : forall Q rd, {{[ wp_mfhi rd Q ]}} mfhi rd {{[ Q ]}}
| hoare0_mflhxu : forall rd Q, {{[ wp_mflhxu rd Q ]}} mflhxu rd {{[ Q ]}}
| hoare0_mflo : forall Q rd, {{[ wp_mflo rd Q ]}} mflo rd {{[ Q ]}}
| hoare0_movn : forall Q rd rs rt, {{[ wp_movn rd rs rt Q ]}} movn rd rs rt {{[ Q ]}}
| hoare0_movz : forall Q rd rs rt, {{[ wp_movz rd rs rt Q ]}} movz rd rs rt {{[ Q ]}}
| hoare0_msubu : forall Q rs rt, {{[ wp_msubu rs rt Q ]}} msubu rs rt {{[ Q ]}}
| hoare0_mthi : forall Q rs, {{[ wp_mthi rs Q ]}} mthi rs {{[ Q ]}}
| hoare0_mtlo : forall Q rs, {{[ wp_mtlo rs Q ]}} mtlo rs {{[ Q ]}}
| hoare0_multu : forall Q rs rt, {{[ wp_multu rs rt Q ]}} multu rs rt {{[ Q ]}}
| hoare0_nor : forall Q rd rs rt, {{[ wp_nor rd rs rt Q ]}} nor rd rs rt {{[ Q ]}}
| hoare0_or : forall Q rd rs rt, {{[ wp_or rd rs rt Q ]}} cmd_or rd rs rt {{[ Q ]}}
| hoare0_sll : forall Q rx ry sa, {{[ wp_sll rx ry sa Q ]}} sll rx ry sa {{[ Q ]}}
| hoare0_sllv : forall Q rd rs rt, {{[ wp_sllv rd rs rt Q ]}} sllv rd rs rt {{[ Q ]}}
| hoare0_sltu : forall Q rd rs rt, {{[ wp_sltu rd rs rt Q ]}} sltu rd rs rt {{[ Q ]}}
| hoare0_sra : forall Q rd rt sa, {{[ wp_sra rd rt sa Q ]}} sra rd rt sa {{[ Q ]}}
| hoare0_srl : forall Q rd rt sa, {{[ wp_srl rd rt sa Q ]}} srl rd rt sa {{[ Q ]}}
| hoare0_srlv : forall Q rd rt rs, {{[ wp_srlv rd rt rs Q ]}} srlv rd rt rs {{[ Q ]}}
| hoare0_subu: forall Q rs rt rd , {{[ wp_subu rd rs rt Q ]}} subu rd rs rt {{[ Q ]}}
| hoare0_sw : forall rt off base Q, {{[ wp_sw rt off base Q ]}} sw rt off base {{[ Q ]}}
| hoare0_xor : forall Q rd rs rt, {{[ wp_xor rd rs rt Q ]}} xor rd rs rt {{[ Q ]}}
| hoare0_xori : forall Q rt rs imm, {{[ wp_xori rt rs imm Q ]}} xori rt rs imm {{[ Q ]}}
where "{{[ P ]}} c {{[ Q ]}}" := (hoare0 P c Q) : mips_hoare_scope.

(** Semantics for total correctness *)
Notation "'hoare_semantics_total'" := (@while.hoare_semantics_total store.t heap.t _ exec0 _
  (fun eb s => eval_b eb (fst s)))
  : mips_hoare_scope.

Lemma soundness0_total : forall (P Q : assert) c, {{[ P ]}} c {{[ Q ]}} ->
  hoare_semantics_total P c Q.
Proof.
move=> P Q c; elim => //; clear P Q c; rewrite /hoare_semantics_total.
- (* nop *) move=> P s h HP.
  exists s; exists h; split=> //.
  by do 2 constructor.
- (* add *) move=> P rt rs rd s h; rewrite /wp_add; case=> H1 H2.
  move: (exec0_add s h rd rt rs H1).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* addi *) move=> P rt rs imm s h; rewrite /wp_addi; case=> H1 H2.
  move: (exec0_addi s h rt rs imm H1).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* addiu *) move=> P rt rs imm s h; rewrite /wp_addiu; move=> H1.
  move: (exec0_addiu s h rt rs imm).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* addu *) move=> Q rs rt rd s h; rewrite /wp_addu; move=> H1.
  move: (exec0_addu s h rd rs rt).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* and *) move=> Q rd rs rt s h; rewrite /wp_and; move=> H1.
  move: (exec0_and s h rd rs rt).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* andi *) move=> Q rt rs imm s h; rewrite /wp_andi; move=> H1.
  move: (exec0_andi s h rt rs imm).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* lw *) move=> P rt off base s h; rewrite /wp_lw; case=> p [H1 [z [H2 H3]]].
  move: (exec0_lw s h rt off base p z H1 H2).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [ constructor; auto | auto] end.
- (* lwxs *) move=> rt idx base P s h; rewrite /wp_lwxs; case=> p [H1 [z [H2 H3]]].
  move: (exec0_lwxs s h rt idx base p z H1 H2).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [ constructor; auto | auto] end.
- (* maddu *) move=> Q rs rt s h H1.
  move: (exec0_maddu s h rs rt).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* mfhi *) move=> Q rd s h H1.
  move: (exec0_mfhi s h rd).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* mflhxu *) move=> rd P s h H1.
  move: (exec0_mflhxu s h rd).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* mflo *) move=> Q rd s h H1.
  move: (exec0_mflo s h rd).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* movn *) move=> Q rd rs rt s h H1.
  case: (MachineInt.dec_int [rt]_s zero32) => X.
  move: (exec0_movn_false s h rd rs rt X).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | apply H1 => //] end.
  move: (exec0_movn_true s h rd rs rt X).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | apply H1 => // ] end.
- (* movz *) move=> Q rd rs rt s h H1.
  case: (MachineInt.dec_int [rt]_s zero32) => X.
  move: (exec0_movz_true s h rd rs rt X).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | apply H1 => //] end.
  move: (exec0_movz_false s h rd rs rt X).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | apply H1 => // ] end.
- (* msubu *) move=> Q rs rt s h H1.
  move: (exec0_msubu s h rs rt).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* mthi *) move=> Q rs s h H1.
  move: (exec0_mthi s h rs).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* mtlo *) move=> Q rs s h H1.
  move: (exec0_mtlo s h rs).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* multu *) move=> Q rs rt s h H1.
  move: (exec0_multu s h rs rt).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* nor *) move=> Q rd rs rt s h; rewrite /wp_nor => H1.
  move: (exec0_nor s h rd rs rt).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* or *) move=> Q rd rs rt s h; rewrite /wp_or => H1.
  move: (exec0_or s h rd rs rt).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* sll *) move=> Q rx ry sa s h; rewrite /wp_sll; move=> H1.
  move: (exec0_sll s h rx ry sa).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* sllv *) move=> Q rd rs rt s h; rewrite /wp_sll; move=> H1.
  move: (exec0_sllv s h rd rs rt).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* sltu *) move=> Q rd rs rt s h; rewrite /wp_sltu; move=> H1.
  move: H1 (exec0_sltu s h rd rs rt).
  move X : (Zlt_bool (u2Z [rs]_s) (u2Z [rt]_s)) => t HQ Y.
  destruct t.
  + exists (store.upd rd one32 s), h.
    split => //; by apply while.exec_cmd0, Y.
  + exists (store.upd rd zero32 s), h.
    split => //; by apply while.exec_cmd0, Y.
- (* sra *) move=> Q rd rt sa s h; rewrite /wp_sra; move=> H1.
  move: (exec0_sra s h rd rt sa).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* srl *) move=> Q rd rt sa s h; rewrite /wp_srl; move=> H1.
  move: (exec0_srl s h rd rt sa).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* srlv *) move=> Q rd rt rs s h; rewrite /wp_srlv; move=> H1.
  move: (exec0_srlv s h rd rt rs).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* subu *) move=> Q rs rt rd s h; rewrite /wp_subu; move=> H1.
  move: (exec0_subu s h rd rs rt).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* sw *) move=> rt offset base P s h; rewrite /wp_sw; case=> l [H1 [z H2]].
  move: (exec0_sw s h rt offset base l H1) => X.
  exists s; exists (heap.upd l [rt]_s h); split=> //.
  by apply while.exec_cmd0, X.
- (* xor *) move=> Q rd rs rt s h; rewrite /wp_xor => H1.
  move: (exec0_xor s h rd rs rt).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
- (* xori *) move=> Q rt rs imm s h; rewrite /wp_xor => H1.
  move: (exec0_xori s h rt rs imm).
  match goal with | _ : _ |- _ -- _ ----> Some (?s', ?h') ->  _ => move=> Htmp;
  exists s', h'; split; [do 2 constructor; auto | auto ] end.
Qed.

(** Semantics for partial correctness *)
Notation "'hoare_semantics'" := (@while.hoare_semantics store.t heap.t _ exec0 _
  (fun eb s => eval_b eb (fst s))) : mips_hoare_scope.

(** Soundness for partial correctness *)
Lemma soundness0 : forall P Q c, {{[ P ]}} c {{[ Q ]}} -> hoare_semantics P c Q.
Proof.
move=> P Q c; move/soundness0_total.
rewrite /hoare_semantics_total => H s h HP; split=> [|s' h' exec_Some].
- case: (H s h HP) => // s' [h' [exec_Some HQ]] exec_None.
  move/semop_prop_m.exec_cmd0_inv : exec_Some => exec_Some.
  move/semop_prop_m.exec_cmd0_inv : exec_None => exec_None.
  (* TODO: shouldn't we call exec0_deter indirectly by the interface in while.v? *)
  by move: (mips_cmd.exec0_deter _ _ _ exec_Some _ exec_None).
- case: (H s h HP) => // s'_ [h'_ [exec_Some' HQ]].
  move/semop_prop_m.exec_cmd0_inv : exec_Some' => exec_Some'.
  move/semop_prop_m.exec_cmd0_inv : exec_Some => exec_Some.
  by case: (mips_cmd.exec0_deter _ _ _ exec_Some _ exec_Some')=> -> ->.
Qed.

(** * Completeness for Partial Correctness *)

Notation "'wp_semantics'" := (@while.wp_semantics store.t heap.t _ exec0 _
  (fun eb s => eval_b eb (fst s)))
  : mips_hoare_scope.

Notation "{{ P }} c {{ Q }}" := (@while.hoare store.t heap.t cmd0 _
  (fun eb s => eval_b eb (fst s)) hoare0 P c Q)
  (at level 82, no associativity) : mips_hoare_scope.

Lemma wp_semantics_sound0 : forall (c : cmd0) Q, {{ wp_semantics c Q }} c {{ Q }}.
Proof.
induction c => Q; match goal with |- {{ ?P }} ?c {{ ?Q }} => eapply while.hoare_conseq with (Q' := Q); [done | idtac | do 3 constructor] end.
- (* nop *) red; intros.
  inversion_clear H.
  apply H1.
  by do 2 constructor.
- (* add *) move=> s h H.
  rewrite /wp_add.
  rewrite /wp_semantics in H.
  case: H => [H1 H2].
  move/exec0_not_None_to_exec_not_None : H1.
  move/exec0_add_not_None => H1.
  split; first by exact H1.
  apply H2; by do 2 constructor.
- (* addi *) move=> s h H.
  rewrite /wp_addi.
  rewrite /wp_semantics in H.
  case: H => H1 H2.
  move/exec0_not_None_to_exec_not_None : H1.
  move/exec0_addi_not_None => H1.
  split; first by exact H1.
  apply H2; by do 2 constructor.
- (* addiu *) move=> s h.
  inversion_clear 1.
  rewrite /wp_addiu.
  apply H1; by do 2 constructor.
- (* addu *) move=> s h.
  inversion_clear 1.
  rewrite /wp_addu.
  apply H1; by do 2 constructor.
- (* cmd_and *) move=> s h.
  inversion_clear 1.
  rewrite /wp_and.
  apply H1; by do 2 constructor.
- (* andi *) move=> s h.
  inversion_clear 1.
  rewrite /wp_andi.
  apply H1; by do 2 constructor.
- (* lw *) move=> s h.
  inversion_clear 1.
  rewrite /wp_lw.
  move/exec0_not_None_to_exec_not_None : H0.
  case/exec0_lw_not_None => x [H [x0 H2]].
  exists x; split => //; exists x0; split => //.
  apply H1; constructor.
  by econstructor; eauto.
- (* lwxs *) move=> s h.
  inversion_clear 1.
  rewrite /wp_lwxs.
  move/exec0_not_None_to_exec_not_None : H0.
  case/exec0_lwxs_not_None => x [H [ x0 H2]].
  exists x; split => //; exists x0; split => //.
  apply H1; constructor.
  by econstructor; eauto.
- (* maddu *) move=> s h.
  inversion_clear 1.
  rewrite /wp_maddu.
  apply H1; by do 2 constructor.
- (* mfhi *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* mflhxu *) move=> s h.
  inversion_clear 1.
  rewrite /wp_mflhxu.
  apply H1; by do 2 constructor.
- (* mflo *) move=> s h.
  inversion_clear 1.
  rewrite /wp_mflo.
  apply H1; by do 2 constructor.
- (* movn *) move=> s h.
  inversion_clear 1.
  rewrite /wp_movn.
  split => H2.
  apply H1; by do 2 constructor.
  apply H1; by do 2 constructor.
- (* movz *) red; intros.
  inversion_clear H.
  red; intros.
  split => H2.
  apply H1; by do 2 constructor.
  apply H1; by do 2 constructor.
- (* msubu *) red; intros.
  inversion_clear H.
  rewrite /wp_msubu.
  apply H1; by do 2 constructor.
- (* mtlhi *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* mtlo *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* multu *) red; intros.
  inversion_clear H.
  rewrite /wp_multu.
  apply H1; by do 2 constructor.
- (* nor *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* cmd_or *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* sll *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* sllv *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* sltu *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* sra *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* srl *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* srlv *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* subu *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* sw *) red; intros.
  inversion_clear H.
  red; intros.
  move/exec0_not_None_to_exec_not_None : H0.
  case/exec0_sw_not_None => x [H [x0 H2]].
  exists x; split => //; split.
  exists x0 => //.
  apply H1.
  constructor.
  by econstructor; eauto.
- (* xor *) red; intros.
  inversion_clear H.
  red; intros.
  apply H1; by do 2 constructor.
- (* xori *) red; intros.
  inversion_clear H.
  rewrite /wp_xori.
  apply H1; by do 2 constructor.
Qed.

(** * Semantics of Separation Logic *)

Module WMIPS_Hoare <: while.WHILE_HOARE_DETER.

Include WMIPS_Semop.

Definition assert := store -> heap -> Prop.

Definition wp0 : cmd0 -> assert -> assert := wp0.
Definition wp0_no_err : forall s h c P,
  wp0 c P s h -> ~ (Some (s,h) -- c ----> None) := wp0_no_err.
Definition exec0_wp0 : forall s h (c : cmd0) s' h', Some (s, h) -- c ----> Some (s', h') ->
  forall P, wp0 c P s h <-> P s' h' := exec0_wp0.

Definition hoare0 : assert -> cmd0 -> assert -> Prop := hoare0.
Definition hoare : assert -> cmd -> assert -> Prop := @while.hoare store heap cmd0 _ eval_b hoare0.

Definition soundness0 : forall P Q c, hoare0 P c Q -> hoare_semantics P c Q := soundness0.

Definition wp_semantics_sound0 : forall (c : cmd0) P, {{ wp_semantics c P }} c {{ P }} :=
  wp_semantics_sound0.

Definition exec0_deter : forall (st : option state) (c : cmd0) (st' : option state),
  st -- c ----> st' ->
  forall st'', st -- c ----> st'' -> st' = st'' := exec0_deter.

End WMIPS_Hoare.

(*Local Close Scope temp_mips_hoare_scope.*)

(*Notation "'wp_semantics'" := (@while.wp_semantics store.t heap.t _ exec0 _
  (fun eb s => eval_b eb (fst s))) : mips_hoare_scope.*)

(*Notation "{{ P }} c {{ Q }}" := (@while.hoare store.t heap.t cmd0 _
  (fun eb s => eval_b eb (fst s)) hoare0 P c Q)
  (at level 82, no associativity) : mips_hoare_scope.*)

(*Notation "'hoare_semantics'" := (@while.hoare_semantics store.t heap.t _ exec0 _
  (fun eb s => eval_b eb (fst s))) : mips_hoare_scope.*)

Module hoare_prop_m := while.While_Hoare_Prop WMIPS_Hoare.

Lemma soundness : forall P Q c, {{ P }} c {{ Q }} -> hoare_semantics P c Q.
Proof. exact hoare_prop_m.soundness. Qed.

Lemma wp_semantics_sound: forall c Q, {{ wp_semantics c Q }} c {{ Q }}.
Proof. exact hoare_prop_m.wp_semantics_sound. Qed.

Lemma hoare_complete : forall P Q c, hoare_semantics P c Q -> {{ P }} c {{ Q }}.
Proof. exact hoare_prop_m.hoare_complete. Qed.

(** * Total Correctness and its Soundness *)

Notation "{{{ P }}} c {{{ Q }}}" := (@while.hoare_total store.t heap.t cmd0 _
  (fun eb s => eval_b eb (fst s)) hoare0 P c Q) (at level 82, no associativity) : mips_hoare_scope.

Lemma hoare_total_sound : forall P Q c, {{{ P }}} c {{{ Q }}} -> hoare_semantics_total P c Q.
Proof. move=> P Q c H. by apply (hoare_prop_m.hoare_total_sound' soundness0_total). Qed.

Lemma hoare_ifte_bang P Q t c d :
  {{ P ** !(eval_b t) }} c {{ Q }} ->
  {{ P ** !(fun s => ~~ eval_b t s) }} d {{ Q }} ->
  {{ P }} If t Then c Else d {{ Q }}.
Proof.
move=> H1 H2.
apply while.hoare_ifte.
- eapply hoare_prop_m.hoare_stren; last by apply H1.
  move=> s h /= H.
  exists h, heap.emp.
  split; first by apply heap.disjhe.
  split; first by rewrite heap.unionhe.
  rewrite /bang.
  tauto.
- eapply hoare_prop_m.hoare_stren; last by apply H2.
  move=> s h /= H.
  exists h, heap.emp.
  split; first by apply heap.disjhe.
  split; first by rewrite heap.unionhe.
  rewrite /bang.
  tauto.
Qed.

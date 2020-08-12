(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import div path tuple.
Require Import Init_ext ssrZ ZArith_ext String_ext Max_ext.
Require Import machine_int seq_ext ssrnat_ext tuple_ext path_ext.
Require order finmap.
Import MachineInt.
Require Import C_types C_types_fp C_value.

Declare Scope C_expr_scope.

Local Close Scope Z_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope C_types_scope.

Definition env_get str {g} (s : g.-env) : option (g.-typ) := assoc_get str s.

Inductive binop_ne : Set := and_e | shl_e | or_e | add_e | sub_e | mul_e.

Inductive binop_re : Set := neq_e | eq_e | lt_e | le_e | gt_e | ge_e | lor_e | land_e.

Definition conversion_rank (t : integral) : nat :=
  match t with
    | ulong => 50
    | uint => 40
    | sint => 40
    | uchar => 20
    | schar => 20
  end.

Definition is_signed (t : integral) : bool :=
  match t with
    | uint => false
    | sint => true
    | uchar => false
    | schar => true
    | ulong => false
  end.

Module UnConv.

(** safe unary conversion *)

Definition safe t1 t2 :=
  if t1 == t2 then
    true
  else if (~~ is_signed t1) && (sizeof_integral t1 < sizeof_integral t2) then
    true (* NB: do zero-extend *)
  else if is_signed t1 && is_signed t2 && (sizeof_integral t1 <= sizeof_integral t2) then
    true (* NB: do sign-extend *)
  else
    false.

(** unary conversion : potential data loss *)

Definition data_loss t1 t2 :=
  if (~~ is_signed t1) && (sizeof_integral t2 < sizeof_integral t1) then
    true (* preserve low-order bits *)
  else if is_signed t1 && is_signed t2 && (sizeof_integral t2 < sizeof_integral t1) then
    true (* preserve low-order bits *)
  else if is_signed t1 && (~~ is_signed t2) && (sizeof_integral t2 < sizeof_integral t1) then
    true (* sign-extend to corresponding signed t2, then convert to unsigned *)
  else
    false.

(** unary conversion : potential incorrect interpretation *)

Definition misinterpret t1 t2 :=
  if (~~ is_signed t1) && is_signed t2 && (sizeof_integral t1 == sizeof_integral t2) then
    true (* NB: preserve bit pattern; high-order bit becomes sign bit *)
  else
  if is_signed t1 && (~~ is_signed t2) && (sizeof_integral t1 == sizeof_integral t2) then
    true (* NB: preserve bit pattern; high-order bit loses function as sign bit *)
  else
    false.

Lemma potential_unsafe_not_safe : forall a b,
  data_loss a b || misinterpret a b -> ~~ safe a b.
Proof. by move=> [] []. Qed.

Goal forall a b, data_loss a b -> ~~ misinterpret a b.
Proof. by move=> [] []. Abort.

Goal forall a b, misinterpret a b -> ~~ data_loss a b.
Proof. by move=> [] []. Abort.

Goal forall a b, safe a b -> ~~ data_loss a b.
Proof. by move=> [] []. Abort.

Goal forall a b, safe a b -> ~~ misinterpret a b.
Proof. by move=> [] []. Abort.

End UnConv.

(** Modulo operation
    This is a specialized version for powers of 2
    E.g.,
    <<
    ciph_len mod 2 != 0
    >>
    becomes
    <<
    (bopk_ne mod2n_e (var_e "ciph_len") 1) \!= cst32_0
    >>
    because 2 is 2^1 *)
(* TODO: generalize the modulo operation to mod_e (%) : expr -> expr -> int such that:
   4 % 3 -> 1
   4 % 4 -> 0
   4 % -? -> undefined *)

Inductive binopk_e : Set := mod2n_e.

Definition binopk_e_interp b {n} (x : int n) (k : nat):=
  match b with
    | mod2n_e => (@rem n _ (@rem k _ x))
  end.

(* TODO: generalize ifte_e condition to any integral type? *)
(* TODO: constructor for hexadecimal constants? *)
Local Open Scope C_value_scope.

Section exp_sect.

Variables (g : wfctxt) (sigma : g.-env).

Inductive exp : g.-typ -> Type :=
| var_e : forall str t, env_get str sigma = |_ t _| -> exp t
| cst_e : forall t, t.-phy -> exp t
| bop_n : forall t, binop_ne -> (* numerical operators *)
  exp (ityp: t) -> exp (ityp: t) -> exp (ityp: t)
| bopk_n : forall t, binopk_e ->
  exp (ityp: t) -> nat -> exp (ityp: t)
| bop_r : forall t, binop_re -> (* relational operators *)
  exp (ityp: t) -> exp (ityp: t) -> exp (g.-ityp: uint)
| add_p : forall t, exp (:* t) -> exp (ityp: sint) -> exp (:* t)
| safe_cast : forall t t', exp (ityp: t) ->
  UnConv.safe t t' -> exp (ityp: t')
| unsafe_cast : forall t t', exp (ityp: t) ->
  UnConv.data_loss t t' ||
  UnConv.misinterpret  t t' -> exp (ityp: t')
| fldp : forall f tg (t : g.-typ) (e : exp (:* t)) (H : styp tg = t) t',
  assoc_get f (get_fields g tg) = |_ t' _| ->
  exp (:* t')
| eq_p : forall t, exp (:* t) -> exp (:* t) -> exp (g.-ityp: uint)
| ifte_e : forall t, exp (ityp: uint) -> exp t -> exp t -> exp t.

End exp_sect.

Arguments exp [g] _ _.
Arguments var_e [g] _ _ _ _.
Arguments cst_e [g] _ _ _.
Arguments bop_n [g] _ _ _ _ _.
Arguments bopk_n [g] _ _ _ _ _.
Arguments bop_r [g] _ _ _ _ _.
Arguments add_p [g] _ _ _ _.
Arguments safe_cast [g] _ _ _ _ _.
Arguments unsafe_cast [g] _ _ _ _ _.
Arguments fldp [g] _ _ [tg] [t] _ _ [t'] _.
Arguments eq_p [g] _ _ _ _.
Arguments ifte_e [g] _ _ _ _ _.

Section vars_sect.

Variable (g : wfctxt) (sigma : g.-env).

Fixpoint vars {t : g.-typ} (e : exp sigma t) : g.-env :=
match e with
  | var_e v t' H => (v, t') :: nil
  | cst_e _ _ => nil
  | bop_n _ _ e1 e2 => vars e1 ++ vars e2
  | bopk_n _ _ e' _ => vars e'
  | bop_r _ _ e1 e2 => vars e1 ++ vars e2
  | add_p _ e1 e2 => vars e1 ++ vars e2
  | safe_cast t t' e' t'_leq_t => vars e'
  | unsafe_cast t t' e' t'_leq_t => vars e'
  | fldp str tg t e' H t' Hin => vars e'
  | eq_p t e1 e2 => vars e1 ++ vars e2
  | ifte_e _ e1 e2 e3 => vars e1 ++ vars e2 ++ vars e3
end.

End vars_sect.

Arguments vars [g sigma] [t] _.

Lemma vars_in_ts {g sigma} {t : g.-typ} (e : exp sigma t) : { subset vars e <= sigma }.
Proof.
elim: e => [ v t0 H x | // | op t0 e1 H1 e2 H2 x | // | op t0 e1 H1 e2 H2 x | t0 e1 H1 e2 H2 x | // | // | // | t0 e1 H1 e2 H2 x | t0 e1 H1 e2 H2 e4 H3 x ].
- rewrite in_cons; case/orP => // /eqP => ?; subst x; by apply: assoc_get_in H.
- rewrite mem_cat; case/orP; by [apply H1 | apply H2].
- rewrite mem_cat; case/orP; by [apply H1 | apply H2].
- rewrite mem_cat; case/orP; by [apply H1 | apply H2].
- rewrite mem_cat; case/orP; by [apply H1 | apply H2].
- rewrite mem_cat; case/orP; [ by apply H1 | ].
  rewrite mem_cat; case/orP; by [apply H2 | apply H3].
Qed.

Notation "'[' pv ']c'" := (cst_e _ _ pv) (at level 9, format "'[' [  pv  ]c ']'") : C_expr_scope.
Local Open Scope C_expr_scope.

Notation "'[' i ']pc'" := ([ [ i ]p ]c) (at level 9, format "'[' [  i  ]pc ']'") : C_expr_scope.

Notation "'[' z ']sc'" := ([ [ z ]s ]c) (at level 9, format "'[' [  z  ]sc ']'") : C_expr_scope.
Notation "'[' z ']uc'" := ([ [ z ]u ]c) (at level 9, format "'[' [  z  ]uc ']'") : C_expr_scope.

Structure Cadd g (sigma : g.-env) :=
  { Cadd_t1 : g.-typ ;
    Cadd_t2 : g.-typ ;
    Cadd_add : exp sigma Cadd_t1 -> exp sigma Cadd_t2 -> exp sigma Cadd_t1 }.

Canonical Structure Cadd_i g sigma t :=
  Build_Cadd g sigma (ityp: t) (ityp: t) (bop_n sigma t add_e).

Canonical Structure Cadd_p g sigma t :=
  Build_Cadd g sigma (:* t) (ityp: sint) (add_p sigma t).

Definition Cadd_add_nosimpl g sigma := nosimpl (Cadd_add g sigma).

Notation "a '\+' b" := (Cadd_add_nosimpl _ _ _ a b) (at level 61, left associativity) : C_expr_scope.

Structure Ceq {g sigma} := {
  Ceq_t : g.-typ ;
  Ceq_eq : exp sigma Ceq_t -> exp sigma Ceq_t -> exp sigma (g.-ityp: uint)}.

Canonical Structure Ceq_i {g sigma} t :=
  @Build_Ceq g sigma (g.-ityp: t) (bop_r sigma t eq_e).

Canonical Structure Ceq_p {g sigma} t :=
  @Build_Ceq g sigma (:* t) (eq_p sigma t).

Definition Ceq_eq_nosimpl {g} {sigma : g.-env} := nosimpl (@Ceq_eq g sigma).

Notation "a '\=' b" := (Ceq_eq_nosimpl _ a b) (at level 64, left associativity) : C_expr_scope.

Notation "a '\&' b" := (bop_n _ _ and_e a b) (at level 65, left associativity) : C_expr_scope.
Notation "a '\|' b" := (bop_n _ _ or_e a b) (at level 66, left associativity) : C_expr_scope.
Notation "a '\-' b" := (bop_n _ _ sub_e a b) (at level 61, left associativity) : C_expr_scope.
Notation "a '\*' b" := (bop_n _ _ mul_e a b) (at level 58, left associativity) : C_expr_scope.
Notation "a '\<<' b" := (bop_n _ _ shl_e a b) (at level 62, left associativity) : C_expr_scope.
Notation "e \% n" := (bopk_n _ _ mod2n_e e n) (at level 57, left associativity) : C_expr_scope.
Notation "a '\!=' b" := (bop_r _ _ neq_e a b) (at level 64, left associativity) : C_expr_scope.
Notation "a '\<' b" := (bop_r _ _ lt_e a b) (at level 63, left associativity) : C_expr_scope.
Notation "a '\<=' b" := (bop_r _ _ le_e a b) (at level 63, left associativity) : C_expr_scope.
Notation "a '\>' b" := (bop_r _ _ gt_e a b) (at level 63, left associativity) : C_expr_scope.
Notation "a '\>=' b" := (bop_r _ _ ge_e a b) (at level 63, left associativity) : C_expr_scope.
Notation "a '\&&' b" := (bop_r _ _ land_e a b) (at level 67, left associativity) : C_expr_scope.
Notation "a '\||' b" := (bop_r _ _ lor_e a b) (at level 68, left associativity) : C_expr_scope.
Notation "e '&->' n" := (@fldp _ _ n _ _ e erefl _ erefl) (at level 56, left associativity) : C_expr_scope.
Notation "e \? f \: g" := (@ifte_e _ _ _ e f g) (at level 69, right associativity) : C_expr_scope.
Notation "'[;' t ';]' e" := (safe_cast _ t e (erefl _)) (at level 6) : C_expr_scope.
Notation "'(int)' e" := (safe_cast _ _ sint e (erefl _)) (at level 6, format "'[' '(int)'  e ']'") : C_expr_scope.
Notation "'{;' t ';}' e" := (unsafe_cast _ _ t e (erefl _)) (at level 6) : C_expr_scope.
Notation "'(UINT)' e" := (unsafe_cast _ _ uint e (erefl _)) (at level 6, format "'[' '(UINT)'  e ']'") : C_expr_scope.

Definition NULL {g} {sigma : g.-env} {t : g.-typ} : exp sigma (:* t) := [ @pv0 g (mkptyp t) ]c.

(** a value store is defined w.r.t. a type_store *)

Record store {g} (sigma : g.-env) :=
  { store_list :> seq (string * {ty : g.-typ & ty.-phy}) ;
    Hstore : map (fun x => (x.1, projT1 x.2)) store_list == sigma }.

Lemma store_irrelevance {g} (sigma : g.-env) : forall (s1 s2 : store sigma),
  store_list sigma s1 = store_list sigma s2 -> s1 = s2.
Proof.
case=> s1 Hs1 [] s2 Hs2 /= ?; subst s2.
congr Build_store; exact: eq_irrelevance.
Qed.

Fixpoint sval_store0 {g} (sigma : g.-env) : seq (string * {t: g.-typ & t.-phy}) :=
  match sigma with
    | nil => nil
    | (n, t) :: tl => (n, existT _ _ (@pv0 _ t)) :: sval_store0 tl
  end.

Lemma rval_store0 {g} : forall (sigma : g.-env),
  map (fun x => (x.1, projT1 x.2)) (sval_store0 sigma) == sigma.
Proof. by elim=> // [[str t] tl] /= /eqP ->. Qed.

Definition store0 {g} (sigma : g.-env) : store sigma :=
  Build_store g sigma (sval_store0 sigma) (rval_store0 sigma).

Lemma env_get_proj_Some {g} : forall (sigma : g.-env) (s : store sigma) str t,
  env_get str (map (fun x => (x.1, projT1 x.2)) s) = |_ t _| ->
  exists y, assoc_get str s = Some y.
Proof.
elim => [ [] // [] // | [str t] tl IH ].
case=> [[|h1 t1] //=] /eqP [] ? ?; subst str t => /eqP H1.
move=> str' t'.
rewrite /env_get /=.
case: ifP => [/eqP ? |/negbT H2 H3].
  subst str'.
  case=> ?; subst t'.
  by exists h1.2.
by apply: IH (Build_store _ _ _ H1) _ t' H3.
Qed.

Lemma env_get_proj_Some2 {g} :
  forall (sigma : g.-env) (s : store sigma) str t y (Hy : y.-phy),
  assoc_get str sigma = |_ t _| -> assoc_get str s  = |_ existT _ y Hy _| ->
  t = y.
Proof.
elim => [ [] // [] // | [str t] tl IH ].
case=> [[|h1 t1] /= Hs] // str' t' y Hy.
case/eqP : Hs => ? ?; subst str t => /eqP Hs.
case: ifP => [/eqP ? | /negbT H2 h3].
  subst str'.
  case=> ?; subst t'.
  by case=> ->.
by move/(IH (Build_store _ _ _ Hs) str' _ _ Hy h3).
Qed.

Section store_sect.

Variables (g : wfctxt) (sigma : g.-env) (str : string) (t : g.-typ).

Lemma store_get_helper (s : store sigma) (Hstr : env_get str sigma = |_ t _|) :
  forall Hl : {l : {i : g.-typ & i.-phy} & assoc_get str s = |_ l _|},
  size (projT2 (projT1 Hl)) = sizeof t.
Proof.
move=> [] /= [] t' pv /=.
case: s => s Hs /=.
move/eqP in Hs; subst sigma.
rewrite /env_get in Hstr.
rewrite (Hphy _ pv) => H1.
suff ? : t' = t by subst.
elim: s t t' pv H1 Hstr => // h1 t1 IH t_ t' pv /=.
case: ifP => [/eqP ? | /negbT H1].
  subst str.
  by case => -> [].
by apply IH.
Qed.

Lemma store_get_helper2 (s : store sigma) (Hstr : env_get str sigma = |_ t _|) :
 assoc_get str s = None -> False.
Proof.
case: s => s Hs /= H1.
move/eqP in Hs; subst sigma.
rewrite /env_get in Hstr.
suff : assoc_get str (map (fun x => (x.1, projT1 x.2)) s) = None by rewrite Hstr.
elim: s Hstr H1 => // h1 t1 IH /=.
by case: ifP.
Qed.

Definition store_get (Hstr : env_get str sigma = |_ t _|) (s : store sigma) : t.-phy.
case: (option_dec (assoc_get str s)).
- move=> Hl.
  apply mkPhy with (phy2seq (projT2 (projT1 Hl))).
  apply store_get_helper.
  exact Hstr.
- move=> Hneq.
  apply False_rect.
  apply (store_get_helper2 _ Hstr Hneq).
Defined.

Lemma store_upd_helper (Hstr : env_get str sigma = |_ t _|) (s : store sigma) val :
  map (fun x => (x.1, projT1 x.2)) (assoc_upd str (existT _ t val) s) == sigma.
Proof.
destruct s as [s Hs] => /=.
move/eqP in Hs; subst sigma.
elim: s t val Hstr => // h1 t1 IH ty val H /=.
case: ifP.
  move/eqP => ?; subst str => /=.
  rewrite /env_get /= eqxx in H.
  by case: H => <-.
move/negbT => H1 /=.
apply/eqP.
congr cons.
apply/eqP/IH.
by rewrite /env_get /= (negbTE H1) in H.
Qed.

Definition store_upd (Hstr : env_get str sigma = |_ t _|) val s :=
  Build_store _ _ _ (store_upd_helper Hstr s val).

Lemma store_get_upd_eq (H : env_get str sigma = |_ t _|) val s :
  store_get H (store_upd H val s) = val.
Proof.
rewrite /store_get /store_upd /=.
case: option_dec => [ | Hcontr] /=.
- case; move=> [x [phy2seq Hphy]] e.
  apply mkPhy_irrelevance => /=.
  have [y Hy] : exists y, assoc_get str s = Some y.
    apply (env_get_proj_Some _ s str t).
    case: s e => s Hs /= e.
    move/eqP in Hs; by subst sigma.
  rewrite (@assoc_get_upd_eq _ _ _ _ _ y) // in e.
  case: e => ?; subst t => H1.
  apply Eqdep.EqdepTheory.inj_pair2 in H1; by subst val.
- suff: False by done.
  move: (env_get_proj_Some _ s str t).
  case: s Hcontr => s Hs /= Hcontr.
  move/eqP in Hs; subst sigma.
  case/(_ H) => y Hy.
  by rewrite (@assoc_get_upd_eq _ _ _ _ _ y) // in Hcontr.
Qed.

Lemma store_upd_get_eq (Hstr : assoc_get str sigma = |_ t _|) s :
  store_upd Hstr (store_get Hstr s) s = s.
Proof.
apply store_irrelevance => /=.
rewrite /store_get /=.
have [y Hy] : exists y, assoc_get str s = Some y.
  apply: env_get_proj_Some sigma _ _ t _.
  case: s => s Hs /=.
  by move/eqP : Hs => ->.
case: option_dec => /= s0.
  apply assoc_upd_inv.
  rewrite [X in X = _]Hy; congr Some.
  case: s0 => s0 Hs0 /=.
  have ? : y = s0 by rewrite Hs0 in Hy; case: Hy.
  subst s0.
  case: y Hy Hs0 => y Hy Hs0 Hy_.
  have ? : y = t by rewrite (env_get_proj_Some2 _ _ _ _ _ _ Hstr Hy_).
  subst y.
  congr existT.
  by apply mkPhy_irrelevance.
apply assoc_upd_inv; by rewrite s0 in Hy.
Qed.

End store_sect.

Arguments store_get [g] [sigma] [str] [t] _ _.
Arguments store_upd [g] [sigma] [str] [t] _ _ _.

Lemma store_get_upd_neq {g} {sigma : g.-env} (s : store sigma) str1 t str2  val
  (H1 : env_get str1 sigma = Some t) ty' (H2 : env_get str2 sigma = Some ty') :
  str1 <> str2 ->
  store_get H2 (store_upd H1 val s) = store_get H2 s.
Proof.
move=> str1_str2.
rewrite /store_get /store_upd /=.
move Heq : (option_dec (assoc_get str2 (assoc_upd str1 (existT phy t val) s))) => [s'|].
- case: s' Heq => [[i [lst Hlst]] /= Hl] Heq.
  move: (not_eq_sym str1_str2) => {}str1_str2.
  move Heq_rhs : (option_dec (assoc_get str2 s)) => [s'|].
  + case: s' Heq_rhs => [[i' [lst' Hlst']] Hl'] Heq_rhs .
    have ? : lst = lst'.
      rewrite {Heq Heq_rhs}.
      rewrite assoc_get_upd_neq // in Hl.
      rewrite Hl in Hl'.
      by case: Hl'.
    subst lst'.
    by apply mkPhy_irrelevance.
  + suff : False by done.
    clear Heq.
    by rewrite assoc_get_upd_neq // Heq_rhs in Hl.
- rewrite /False_rect /=.
  by case: store_get_helper2.
Qed.

Program Definition safe_cast_phy_sint {g} (v : (ityp: sint).-phy) (t : integral)
  (H : UnConv.safe sint t) : (ityp: t).-phy :=
  match t with
    | sint => v
    | uint => @False_rect _ _
    | uchar => @False_rect _ _
    | schar => @False_rect _ _
    | ulong => match v with
                 mkPhy l Hl => mkPhy (g.-ityp: ulong)
                 match oi32<=i8 l with
                   | Some i => i8<=i64 (sext (8 * (sizeof_integral ulong - sizeof_integral sint)) i)
                   | None => @False_rect _ _
                 end _
               end
  end.

Obligation Tactic := idtac.

Program Definition safe_cast_phy_uint {g} (v : (ityp: uint).-phy) (t : integral)
  (H : UnConv.safe uint t) : (ityp: t).-phy :=
  match t with
    | sint => @False_rect _ _
    | uint => v
    | uchar => @False_rect _ _
    | schar => @False_rect _ _
    | ulong => match v return (ityp: ulong).-phy with
                 mkPhy l Hl => mkPhy (g.-ityp: ulong) _ _
               end
  end.
Next Obligation.
Tactics.program_simpl.
Defined.
Next Obligation.
Tactics.program_simpl.
Defined.
Next Obligation.
Tactics.program_simpl.
Defined.
Next Obligation.
intros.
destruct (option_dec (oi32_of_i8 l)) as [s|].
destruct s as [i Hi].
exact (i8_of_i64 (zext (8 * (sizeof_integral ulong - sizeof_integral uint)) i)).
apply False_rect.
case: (@int_flat_Some _ _ _ (refl_equal _) _ Hl).
move: e.
rewrite /oi32_of_i8 sizeof_ityp.
by move=> ->.
Defined.
Next Obligation.
intros.
rewrite /safe_cast_phy_uint_obligation_4.
rewrite /=.
destruct (@option_dec) as [s|].
  destruct s as [i Hi].
  by rewrite sizeof_ityp /= /i8_of_i64 size_int_break.
apply False_rect.
case: (@int_flat_Some _ _ _ Logic.eq_refl _ Hl).
move: e.
rewrite /oi32_of_i8 sizeof_ityp.
by move=> ->.
Defined.

Obligation Tactic := Tactics.program_simpl.

Program Definition safe_cast_phy_uchar {g} (v : (g.-ityp: uchar).-phy) (t : integral)
  (H : UnConv.safe uchar t) : (ityp: t).-phy :=
  match v with
    | mkPhy l Hl =>
      match l with
        | h :: nil =>
          match t with
            | uchar => v
            | schar => mkPhy (ityp: schar) v (Hphy (ityp: schar) v)
            | sint => mkPhy (ityp: sint) (i8<=i32 (zext (8 * (sizeof_integral sint - sizeof_integral uchar)) h)) _
            | uint => mkPhy (ityp: uint) (i8<=i32 (zext (8 * (sizeof_integral uint - sizeof_integral uchar)) h)) _
            | ulong => mkPhy (ityp: ulong) (i8<=i64 (zext (8 * (sizeof_integral ulong - sizeof_integral uchar)) h)) _
          end
        | _ => @pv0 g (g.-ityp: t) (* dummy; shouldn't happen*)
      end
  end.
Next Obligation.
rewrite /i8_of_i32 size_int_break sizeof_ityp.
reflexivity.
Defined.
Next Obligation.
by rewrite /i8_of_i32 size_int_break sizeof_ityp.
Defined.
Next Obligation.
by rewrite /i8_of_i64 size_int_break sizeof_ityp.
Defined.

Lemma safe_cast_phy_uchar_zext {g} (a : @phy g _) H :
  safe_cast_phy_uchar a sint H = [ zext 24 (i8<=phy a) ]p.
Proof.
destruct a as [a Ha].
have Ha' : size a = 1 by rewrite Ha sizeof_ityp.
have Ha'Ha : Ha' = Ha by apply eq_irrelevance.
subst Ha.
destruct a as [|h []] => //=.
by apply mkPhy_irrelevance.
Qed.

Program Definition safe_cast_phy_schar {g} (v : (g.-ityp: schar).-phy) (t : integral)
  (H : UnConv.safe schar t) : (ityp: t).-phy :=
  match v with
    | mkPhy l Hl =>
      match l return (ityp: t).-phy with
        | h :: nil =>
          match t with
            | uchar => @False_rect _ _
            | schar => v
            | sint => mkPhy (ityp: sint)
              (i8_of_i32 (sext (8 * (sizeof_integral sint - sizeof_integral schar)) h)) _
            | uint => @False_rect _ _
            | ulong => @False_rect _ _
          end
        | _ => @pv0 g (g.-ityp: t) (* dummy; shouldn't happen*)
      end
  end.
Next Obligation.
rewrite /i8_of_i32 size_int_break sizeof_ityp.
reflexivity.
Defined.

Program Definition safe_cast_phy {g t} (pv : (g.-ityp: t).-phy)
  t' (H : UnConv.safe t t') : (g.-ityp: t').-phy :=
  match t with
    | sint => safe_cast_phy_sint pv t' H
    | uint => safe_cast_phy_uint pv t' H
    | uchar => safe_cast_phy_uchar pv t' H
    | schar => safe_cast_phy_schar pv t' H
    | ulong => pv
  end.
Next Obligation. by destruct t'. Defined.

Notation "'(phyint)' e" := (safe_cast_phy e sint Logic.eq_refl)
  (at level 6, format "'[' '(phyint)'  e ']'") : C_value_scope.

Lemma si32_of_phy_safe_cast_phy_uchar {g} (a : @phy g _) H :
  si32<=phy (safe_cast_phy a sint H) = zext 24 (i8<=phy a).
Proof.
rewrite /si32_of_phy /safe_cast_phy -2!Eqdep.Eq_rect_eq.eq_rect_eq.
by rewrite safe_cast_phy_uchar_zext /= i8_of_i32Ko /=.
Qed.

Program Definition unsafe_cast_phy {g} {t} (v : (g.-ityp: t).-phy) t'
  (H : UnConv.data_loss t t' || UnConv.misinterpret t t') : (ityp: t').-phy :=
  match (t != t') && (sizeof_integral t == sizeof_integral t') with
    | true =>
      match v with mkPhy l Hl => mkPhy (ityp: t') l _ end
    | false =>
      match is_signed t && ~~ (is_signed t') && (sizeof_integral t < sizeof_integral t') with
        | true => safe_cast_phy v t' _
        | false =>
          match sizeof_integral t' < sizeof_integral t with
            | true => match v with
                        mkPhy l Hl => mkPhy (ityp: t') (drop (sizeof_integral t - sizeof_integral t') l) _
                      end
            | false => @False_rect _ _
          end
      end
  end.
Next Obligation.
move: t t' H Hl Heq_anonymous.
by move=> [] [] //=.
Defined.
Next Obligation.
move: t t' v H Heq_anonymous Heq_anonymous0.
move=> [] [] //=.
Defined.
Next Obligation.
rewrite size_drop Hl.
move: t t' H Hl Heq_anonymous Heq_anonymous0 Heq_anonymous1.
move=> [] [] //=.
Defined.
Next Obligation.
move: t v t' H Heq_anonymous Heq_anonymous0 Heq_anonymous1.
move=> [] [] //=.
by move=> s Hs [].
by move=> s Hs [].
by move=> s Hs [].
by move=> s Hs [].
by move=> s Hs [].
Defined.

Definition binop_ne_interp b {n} : int n -> int n -> int n :=
  match b with
    | and_e => @int_and n
    | or_e => @int_or n
    | shl_e => fun e1 e2 => shl '|u2Z e2| e1
    | add_e => @add n
    | sub_e => @sub n
    | mul_e => @mul n
  end.

(** reasoning over Z, in order to handle unsigned and signed integers in the same manner *)

Definition binop_re_interp b (x y : Z) : int 32 :=
  match b with
    | eq_e => if x == y then Z2u 32 1 else Z2u 32 0
    | neq_e => if x == y then Z2u 32 0 else Z2u 32 1
    | lt_e => if Zlt_bool x y then Z2u 32 1 else Z2u 32 0
    | le_e => if Zle_bool x y then Z2u 32 1 else Z2u 32 0
    | gt_e => if Zlt_bool y x then Z2u 32 1 else Z2u 32 0
    | ge_e => if Zle_bool y x then Z2u 32 1 else Z2u 32 0
    | lor_e => if (x == Z0) && (y == Z0) then Z2u 32 0 else Z2u 32 1
    | land_e => if (x == Z0) || (y == Z0) then Z2u 32 0 else Z2u 32 1
  end.

Local Open Scope machine_int_scope.

Reserved Notation "'[' e ']_' s" (at level 9, format "'[' [  e  ]_ s ']'", no associativity).

Fixpoint eval {g sigma t} (s : store sigma) (e : exp sigma t) : t.-phy :=
  match e with
    | var_e v t H => store_get H s
    | cst_e t v => v
    | bop_r t' b e1 e2 =>
      match t' as t return (forall (_ : t = t'), (ityp: uint).-phy) with
        | uint =>
          match [ e1 ]_ s, [ e2 ]_ s with
            | mkPhy l1 H1, mkPhy l2 H2 => fun (Heq : uint = t') =>
                let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                let H'2 := eq_ind_r (fun t => size l2 = sizeof (ityp: t)) H2 Heq in
                [ binop_re_interp b (u2Z (i32<=i8 l1 H'1)) (u2Z (i32<=i8 l2 H'2)) ]p
          end
        | sint =>
          match [ e1 ]_ s, [ e2 ]_ s with
            | mkPhy l1 H1, mkPhy l2 H2 => fun (Heq : sint = t') =>
                let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                let H'2 := eq_ind_r (fun t => size l2 = sizeof (ityp: t)) H2 Heq in
                [ binop_re_interp b (s2Z (i32<=i8 l1 H'1)) (s2Z (i32<=i8 l2 H'2)) ]p
          end
        | uchar =>
          match [ e1 ]_ s, [ e2 ]_s with
            | mkPhy l1 H1, mkPhy l2 H2 => fun (Heq : uchar = t') =>
                let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                let H'2 := eq_ind_r (fun t => size l2 = sizeof (ityp: t)) H2 Heq in
                [ binop_re_interp b (u2Z (i8_to_i8 l1 H'1)) (u2Z (i8_to_i8 l2 H'2)) ]p
          end
        | schar =>
          match [ e1 ]_ s, [ e2 ]_s with
            | mkPhy l1 H1, mkPhy l2 H2 => fun (Heq : schar = t') =>
                let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                let H'2 := eq_ind_r (fun t => size l2 = sizeof (ityp: t)) H2 Heq in
                [ binop_re_interp b (s2Z (i8_to_i8 l1 H'1)) (s2Z (i8_to_i8 l2 H'2)) ]p
          end
        | ulong =>
          match [ e1 ]_ s, [ e2 ]_ s with
            | mkPhy l1 H1, mkPhy l2 H2 => fun (Heq : ulong = t') =>
                let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                let H'2 := eq_ind_r (fun t => size l2 = sizeof (ityp: t)) H2 Heq in
                [ binop_re_interp b (u2Z (i64<=i8 l1 H'1)) (u2Z (i64<=i8 l2 H'2)) ]p
          end
      end erefl
    | bop_n t' b e1 e2 =>
      match t' as t return (forall (_ : t = t'), (g.-ityp: t).-phy) with
        | uint =>
          match [ e1 ]_ s, [ e2 ]_s with
            | mkPhy l1 H1, mkPhy l2 H2 => fun (Heq : uint = t') =>
                let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                let H'2 := eq_ind_r (fun t => size l2 = sizeof (ityp: t)) H2 Heq in
                [ binop_ne_interp b (i32<=i8 l1 H'1) (i32<=i8 l2 H'2) ]p
          end
        | uchar =>
          match [ e1 ]_ s, [ e2 ]_s with
            | mkPhy l1 H1, mkPhy l2 H2 => fun (Heq : uchar = t') =>
                let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                let H'2 := eq_ind_r (fun t => size l2 = sizeof (ityp: t)) H2 Heq in
                [ binop_ne_interp b (i8_to_i8 l1 H'1) (i8_to_i8 l2 H'2) ]p
          end
        | schar =>
          match [ e1 ]_ s, [ e2 ]_s with
            | mkPhy l1 H1, mkPhy l2 H2 => fun (Heq : schar = t') =>
                let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                let H'2 := eq_ind_r (fun t => size l2 = sizeof (ityp: t)) H2 Heq in
                [ binop_ne_interp b (i8_to_i8 l1 H'1) (i8_to_i8 l2 H'2) ]p
          end
        | sint =>
          match [ e1 ]_ s, [ e2 ]_ s with
            | mkPhy l1 H1, mkPhy l2 H2 => fun (Heq : sint = t') =>
                let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                let H'2 := eq_ind_r (fun t => size l2 = sizeof (ityp: t)) H2 Heq in
                [ binop_ne_interp b (i32<=i8 l1 H'1) (i32<=i8 l2 H'2) ]p
          end
        | ulong =>
          match [ e1 ]_ s, [ e2 ]_ s with
            | mkPhy l1 H1, mkPhy l2 H2 => fun (Heq : ulong = t') =>
                let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                let H'2 := eq_ind_r (fun t => size l2 = sizeof (ityp: t)) H2 Heq in
                [ binop_ne_interp b (i64<=i8 l1 H'1) (i64<=i8 l2 H'2) ]p
          end
      end erefl
    | bopk_n ity b e1 k =>
      match ity as t return (forall (_ : t = ity), (ityp: t).-phy) with
        | uint => match [ e1 ]_ s with
                  | mkPhy l1 H1 => fun (Heq : uint = ity) =>
                    let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                    [ binopk_e_interp b (i32<=i8 l1 H'1) k ]p
                  end
        | sint => match [ e1 ]_ s with
                  | mkPhy l1 H1 => fun (Heq : sint = ity) =>
                    let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                    [ binopk_e_interp b (i32<=i8 l1 H'1) k ]p
                  end
        | uchar => match [ e1 ]_ s with
                   | mkPhy l1 H1 => fun (Heq : uchar = ity) =>
                     let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                     [ binopk_e_interp b (i8_to_i8 l1 H'1) k ]p
                   end
        | schar => match [ e1 ]_ s with
                   | mkPhy l1 H1 => fun (Heq : schar = ity) =>
                     let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                     [ binopk_e_interp b (i8_to_i8 l1 H'1) k ]p
                   end
        | ulong => match [ e1 ]_ s with
                   | mkPhy l1 H1 => fun (Heq : ulong = ity) =>
                     let H'1 := eq_ind_r (fun t => size l1 = sizeof (ityp: t)) H1 Heq in
                     [ binopk_e_interp b (i64<=i8 l1 H'1) k ]p
                   end
      end (Logic.eq_refl _)
     | add_p t e1 e2 =>
      match [ e1 ]_s, [ e2 ]_s with
        | mkPhy l1 H1, mkPhy l2 H2 =>
          let p := ptr<=i8 l1 H1 in
          let k := i32<=i8 l2 H2 in
          phy<=ptr t (add_prod p (sizeof t) (Z<=s k))
      end
    | safe_cast ty ty' e H => safe_cast_phy [ e ]_s ty' H

    | unsafe_cast ty ty' e H => unsafe_cast_phy [ e ]_s ty' H

    | fldp n tg ty e H ty' Hin =>
      shift_pointer _ [ e ]_s _ (field_address 0 n ty' (get_fields g tg) (assoc_get_in Hin))
    | eq_p ty e1 e2 =>
      if [ e1 ]_s == [ e2 ]_s then [ Z2u 32 1 ]p else [ zero32 ]p
    | ifte_e ty' e1 e2 e3 =>
      if is_zero [ e1 ]_s then [ e3 ]_s else [ e2 ]_s
  end
where "'[' e ']_' s" := (eval s e).
Global Opaque eval.

Lemma eval_store_upd_notin {g} sigma t :
  forall (e : exp sigma t) (t' : g.-typ) y (H : env_get y sigma = Some t') pval,
    y \notin unzip1 (vars e) ->
    forall s, [ e ]_ (store_upd H pval s) = [ e ]_ s.
Proof.
Transparent eval.
elim : t / => //.
- move=> x t ts_t t' y ts_t' pval' /= Hy s.
  rewrite store_get_upd_neq // => ?; subst y.
  by rewrite in_cons eqxx /= in Hy.
- move=> b t e1 IH1 e2 IH2 t' y y_t' pval Hyp s.
  rewrite /unzip1 /= map_cat mem_cat negb_or in Hyp.
  case/andP : Hyp => ? ?.
  by rewrite /= IH1 // IH2.
- move=> b it e IH k t' y y_t' pv Hyp s.
  by rewrite /= IH.
- move=> b t e1 IH1 e2 IH2 t' y y_t' pval Hyp s.
  rewrite /unzip1 /= map_cat mem_cat negb_or in Hyp.
  case/andP : Hyp => ? ?.
  by rewrite /= IH1 // IH2.
- (* add_pe *) move=> t e1 IH1 e2 IH2 t' y H pv Hyp s.
  rewrite /unzip1 /= map_cat mem_cat negb_or in Hyp.
  case/andP : Hyp => ? ?.
  by rewrite /= IH1 // IH2.
- move=> t t' e IH Hsz t'' y ts_t'' pval'' /= Hin s; by rewrite IH.
- (* unsafe_cast_e *) move=> t t' e IH Hsz t'' y ts_t'' pval'' /= Hin s; by rewrite IH.
- move=> str tg t tg_t IH r t' Hin' t'' y y_t'' pval'' /= Hy s; by rewrite IH.
- move=> t e1 IH1 e2 IH2 t' y y_t' pval' /= Hyp s.
  rewrite /unzip1 /= map_cat mem_cat negb_or in Hyp.
  case/andP : Hyp => ? ?.
  by rewrite /= IH1 // IH2.
- move=> t e1 IH1 e2 IH2 e3 IH3 t' y y_t' pv Hyp s.
  rewrite /unzip1 /= !map_cat mem_cat negb_or in Hyp.
  case/andP : Hyp => H0.
  rewrite [vars _]/= mem_cat negb_or.
  case/andP => H1 H2.
  by rewrite /= IH1 // IH2 // IH3.
Opaque eval.
Qed.

Definition subst_exp {g} {sigma : g.-env} str {t' : g.-typ} (str_t' : env_get str sigma = |_ t' _|) (e' : exp sigma t')
  {t : g.-typ} (e : exp sigma t) : exp sigma t :=
  exp_rect g sigma
  (fun (t0 : g.-typ) (_ : exp sigma t0) => exp sigma t0)
  (fun str0 (t0 : g.-typ) (e0 : env_get str0 sigma = |_ t0 _|) =>
   match string_dec str0 str with
   | left Heq =>
     let str_t0 :  env_get str sigma = |_ t0 _| := eq_rect str0 (fun x => env_get x sigma = |_ t0 _|) e0 _ Heq in
     (eq_rect t' (exp sigma) e' t0)
       ((f_equal
           (fun ot => match ot with |_ t1 _| => t1 | None => t' end)
           (Logic.trans_eq (Logic.eq_sym str_t') str_t0)) :
          t' = t0)
   | right _ => var_e sigma str0 t0 e0
   end)
  (cst_e sigma)
  (fun t0 b (_ IHe1 _ IHe2 : exp sigma (g.-ityp: t0)) =>
   match b with
   | and_e => IHe1 \& IHe2
   | shl_e => IHe1 \<< IHe2
   | or_e => IHe1 \| IHe2
   | add_e => IHe1 \+ IHe2
   | sub_e => IHe1 \- IHe2
   | mul_e => IHe1 \* IHe2
   end)
  (fun t0 b (_ IHe : exp sigma (g.-ityp: t0)) => bopk_n sigma t0 b IHe)
  (fun t0 b (_ IHe1 _ : exp sigma (g.-ityp: t0)) => bop_r sigma t0 b IHe1)
  (fun t0 (_ IHe1 : exp sigma (:* t0)) _ => fun x => IHe1 \+ x)
  (fun t0 (t'0 : integral) (_ IHe : exp sigma (g.-ityp: t0)) => safe_cast sigma t0 t'0 IHe)
  (fun t0 t'0 (_ IHe : exp sigma (g.-ityp: t0)) => unsafe_cast sigma t0 t'0 IHe)
  (fun f tg t1 (_ IHe : exp sigma (:* t1)) (H : styp tg = t1) (t'1 : g.-typ) =>
     @fldp _ sigma f _ _ IHe H t'1)
  (fun t0 (_ IHe1 _ : exp sigma (:* t0)) => eq_p sigma t0 IHe1)
  (fun t0 (_ IHe1 : exp sigma (g.-ityp: uint)) (_ IHe2 _ : exp sigma t0) => ifte_e sigma t0 IHe1 IHe2)
  t e.

Lemma subst_exp_store_upd  {g} {sigma : g.-env} x {t' : g.-typ}
  {Hx : env_get x sigma = Some t'} (e' : exp sigma t') s {t : g.-typ} (e : exp sigma t) :
  [ subst_exp x Hx e' e ]_ s = [ e ]_ (store_upd Hx ([ e' ]_ s) s).
Proof.
Transparent eval.
elim: t / e => //.
- move=> str t str_t /=.
   case: string_dec => [Heq|Hneq].
  + subst str.
    have ? : t' = t by rewrite Hx in str_t; case: str_t.
    subst t'.
    have ? : Hx = str_t by apply eq_irrelevance.
    subst Hx.
    by rewrite store_get_upd_eq -Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
  + rewrite store_get_upd_neq //; by apply nesym.
- by case=> //; case=> //= => e1 -> e2 ->.
- by move=> t b e /= ->.
- by move=> t b e1 /= -> e2 ->.
- by move=> t e1 /= -> e2 ->.
- by move=> t t_ e1 /= -> i.
- by move=> t t_ e1 /= -> i.
- by move=> f tg t e /= -> _ t_.
- by move=> t e1 /= -> e2 ->.
- by move=> t e1 /= -> e2 -> e3 ->.
Opaque eval.
Qed.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope Z_scope.

Section eval_sect.

Variable (g : wfctxt) (sigma : g.-env).

(* NB: generalize? *)
Lemma eval_spec : forall (a : (:* (g.-ityp: uchar)).-phy),
  [ [phy<=ptr _ (ptr<=phy a `+ `( 8 )_ ptr_len) ]c ]_ (store0 sigma) =
  [ [ a ]c \+ [ 8 ]sc ]_ (store0 sigma).
Proof.
case=> l Hl.
rewrite /ptr_of_phy /=.
case: option_dec => [ [x Hx] |abs].
Transparent eval.
- rewrite /eval /= /phy_of_ptr; apply mkPhy_irrelevance.
  by rewrite /add_prod i8_of_i32K Z2sK //= (optr_of_i8_bij3 _ _ _ Hx).
Opaque eval.
- have [x Hx] : {x | optr<=i8 l = Some x}.
    apply int_flat_Some; by rewrite Hl sizeof_ptyp.
  congruence.
Qed.

Variable (s : store sigma).

Lemma eval_pv t (pv : @phy g t) : [ [ pv ]c ]_s = pv.
Proof. done. Qed.

Lemma size_sc (e : Z) : size [ [ e ]sc : exp sigma (ityp: sint)]_s = 4%nat.
Proof. by rewrite size_int_break. Qed.

Lemma s2Z_sc (e : Z) H : - 2 ^^ 31 <= e < 2 ^^ 31 ->
  Z<=s (i32<=i8 [ [ e ]sc : exp sigma (ityp: sint) ]_s H) = e.
Proof. move=> K. by rewrite i8_of_i32K Z2sK. Qed.

Lemma si32_of_phy_sc n : si32<=phy [ [ n ]sc : exp sigma _ ]_ s = Z2s 32 n.
Proof. by rewrite /si32_of_phy /= /= i8_of_i32Ko. Qed.

Lemma u2Z_si32_of_phy_safe_cast (e : exp sigma (g.-ityp: uchar)) :
  u2Z (si32<=phy [ (int) e ]_ s) = u2Z (i8<=phy [ e ]_s).
Proof.
Transparent eval.
rewrite /= /si32_of_phy /= /safe_cast_phy_uchar.
move He : ([ e ]_s) => [he Hhe].
have Hhe' : size he = 1%nat by rewrite Hhe sizeof_ityp.
destruct he as [|hehd []] => //.
by rewrite /= i8_of_i32Ko /= /i8_of_phy /= (u2Z_zext (8 * (4 - 1))).
Opaque eval.
Qed.

Lemma s2Z_si32_of_phy_safe_cast (e : exp sigma (g.-ityp: uchar)) :
  s2Z (si32<=phy [ (int) e]_ s) = Z<=u (i8<=phy [ e ]_s).
Proof.
Transparent eval.
rewrite /= /si32_of_phy /= /safe_cast_phy_uchar.
move He : ([ e ]_s) => [he Hhe].
have Hhe' : size he = 1%nat by rewrite Hhe sizeof_ityp.
destruct he as [|hehd []] => //.
rewrite /= i8_of_i32Ko /= /i8_of_phy /= s2Z_u2Z_pos'; last first.
  rewrite (u2Z_zext (8 * (4 - 1))).
  split; [exact/min_u2Z | exact: (ltZ_trans (max_u2Z _))].
by rewrite (u2Z_zext (8 * (4 - 1)) hehd).
Opaque eval.
Qed.

Lemma is_zero_or (e1 e2 : exp sigma (ityp: uint)):
  is_zero [ e1 \|| e2 ]_s -> is_zero [ e1 ]_s /\ is_zero [ e2 ]_s.
Proof.
Transparent eval.
rewrite /is_zero /=.
move H1 : ([ e1 ]_s) => [h1 Hh1].
move H2 : ([ e2 ]_s) => [h2 Hh2].
have : size h1 = 4%nat by rewrite Hh1 sizeof_ityp.
case/oi32_of_i8_Some => x Hx.
have : size h2 = 4%nat by rewrite Hh2 sizeof_ityp.
case/oi32_of_i8_Some => y Hy.
case: ifP => [H _ | H].
  case/andP : H => H H'.
  rewrite (_ : Z0 = u2Z zero32) in H; last by rewrite Z2uK.
  move/eqP/u2Z_inj in H.
  rewrite (_ : Z0 = u2Z zero32) in H'; last by rewrite Z2uK.
  move/eqP/u2Z_inj in H'.
  rewrite -H' in H.
  move/i32_of_i8_inj : H => ?; subst h2.
  move/i32_of_i8_bij : H' => ?; subst h1.
  split; apply/eqP; by apply mkPhy_irrelevance.
case/eqP.
move/int_break_inj => K.
by apply Z2u_dis in K.
Opaque eval.
Qed.

Lemma is_zero_or2 (e1 e2 : exp sigma (ityp: uint)) :
  is_zero [ e1 ]_s -> is_zero [ e2 ]_s -> is_zero [ e1 \|| e2 ]_s.
Proof.
Transparent eval.
rewrite /is_zero => /eqP H1 /eqP H2 /=.
by rewrite H1 H2 /= i8_of_i32K Z2uK.
Opaque eval.
Qed.

Lemma add_p_0 (t : g.-typ) (e : exp sigma (:* t)) : [ e \+ [ 0 ]sc ]_ s = [ e ]_ s.
Proof.
Transparent eval.
rewrite /=.
move e_ov : ([ e ]_ s) => [ov Hov].
have : size ov = sizeof_ptr by rewrite Hov sizeof_ptyp.
case/optr_of_i8_Some => v ov_v.
rewrite (optr_of_i8_bij3 _ _ _ ov_v) i8_of_i32K /phy_of_ptr.
apply mkPhy_irrelevance => /=.
rewrite /add_prod Z2sK //= mulZ0 addi0.
by apply optr_of_i8_bij.
Opaque eval.
Qed.

Lemma u2Z_ptyp2ptr_nat (t : g.-typ) (e : exp sigma (:* t)) n :
  - 2 ^^ 31 <= Z_of_nat n < 2 ^^ 31 ->
  u2Z (ptr<=phy [e ]_ s) + Z<=nat (n * sizeof t) < 2 ^^ ptr_len ->
  u2Z (ptr<=phy [e \+ [ Z_of_nat n ]sc ]_ s) = u2Z (ptr<=phy [e ]_ s) + Z<=nat (n * sizeof t).
Proof.
Transparent eval.
move: n; elim => [ | n IH Hn H].
  by rewrite mul0n [Z_of_nat _]/= add_p_0 addZ0.
rewrite /ptr_of_phy 2!optr_of_i8_of_phy Z_S [u2Z _]/= i8_of_i32K.
move Hes : ( [ e ]_ s) => [es es'].
have : size es = sizeof_ptr by rewrite es' sizeof_ptyp.
case/optr_of_i8_Some => x es''.
rewrite (optr_of_i8_bij3 _ _ _ es'') phy_of_ptrK /ptr_of_phy /= es'' /=.
have ty_fit : 0 <= Z_of_nat (n.+1 * sizeof t) < 2 ^^ ptr_len.
  split; first by apply Zle_0_nat.
  move: (min_u2Z (ptr<=phy [e ]_ s)) => ?; lia.
rewrite /add_prod Z2sK; last by rewrite Z_S in Hn.
rewrite (_ : 0 <=? (Z_of_nat n + 1) = true); last by rewrite -Z_S.
rewrite u2Z_add.
+ rewrite Z2uK.
    rewrite mulSn inj_plus inj_mult; ring.
  rewrite mulSn inj_plus inj_mult in ty_fit.
  rewrite Zmult_plus_distr_r Zmult_1_r mulZC; lia.
+ rewrite Z2uK //.
    rewrite Hes [u2Z _]/= /ptr_of_phy [u2Z _]/= es'' [u2Z _]/= in H.
    rewrite inj_mult Z_S in H.
    rewrite mulZC; lia.
  rewrite inj_mult Z_S in ty_fit.
  rewrite mulZC; lia.
Opaque eval.
Qed.

Lemma u2Z_ptyp2ptr_1 (t : g.-typ) (e : exp sigma (:* t)) :
  u2Z (ptr<=phy [e ]_ s) + Z<=nat (sizeof t) < 2 ^^ ptr_len ->
  u2Z (ptr<=phy [e \+ [ 1 ]sc ]_ s) = u2Z (ptr<=phy [e ]_ s) + Z<=nat (sizeof t).
Proof.
move=> H.
rewrite (_ : 1%Z = Z_of_nat 1%nat) // -(mult_1_l (sizeof t)).
apply u2Z_ptyp2ptr_nat => //.
by rewrite mul1n.
Qed.

Lemma eval_add_pA t (a : exp sigma (:* t)) b c :
  0 <= Z<=nat (sizeof t) * s2Z (si32<=phy [ b ]_s) < 2 ^^ 31 ->
  0 <= Z<=nat (sizeof t) * s2Z (si32<=phy [ c ]_s) < 2 ^^ 31 ->
  0 <= Z<=nat (sizeof t) * s2Z (si32<=phy [ b ]_s) +
        Z<=nat (sizeof t) * s2Z (si32<=phy [ c ]_s) < 2 ^^ 31 ->
  [ a \+ b \+ c ]_s = [ a \+ (b \+ c) ]_s.
Proof.
Transparent eval.
move=> b_fit c_fit bc_fit.
move Heval_c : ( [ c ]_s ) => [c' Hc].
move Heval_a : ( [ a ]_s ) => [a' Ha].
move Heval_b : ( [ b ]_s ) => [b' Hb].
rewrite /= Heval_a Heval_c Heval_b /=.
case/optr_of_i8_Some : (Ha) => ptr_a' Hptr_a'.
case/oi32_of_i8_Some : (Hb) => int_b' Hint_b'.
case/oi32_of_i8_Some : (Hc) => int_c' Hint_c'.
rewrite /= (optr_of_i8_bij3 _ _ _ Hptr_a') i8_of_i32K.
congr (phy<=ptr _ _).
set b'' := i32_of_i8 _ _.
set c'' := i32_of_i8 _ _.
have ? : b'' = int_b'.
  rewrite /i32_of_i8.
  apply int_flat_int_flat_ok.
  by rewrite -Hint_b'.
subst int_b'.
have ? : c'' = int_c'.
  rewrite /i32_of_i8.
  apply int_flat_int_flat_ok.
  by rewrite -Hint_c'.
subst int_c'.
rewrite i8_of_ptrK add_prodA //.
- by apply sizeof_gt0.
- move: b_fit; rewrite Heval_b; by rewrite /si32_of_phy /phy2seq Hint_b'.
- move: c_fit; rewrite Heval_c; by rewrite /si32_of_phy /phy2seq Hint_c'.
- move: bc_fit; rewrite Heval_c Heval_b.
  by rewrite /si32_of_phy /phy2seq Hint_c' Hint_b'.
Opaque eval.
Qed.

(* works for \+, \-, \|, \& *)
Lemma si32_of_phy_binop_ne (e1 : exp sigma _) e2 (b : binop_ne) :
  si32<=phy [bop_n sigma sint b e1 e2 ]_ s =
  (binop_ne_interp b) (si32<=phy ([ e1 ]_ s)) (si32<=phy ([ e2 ]_ s)).
Proof.
Transparent eval.
rewrite /=.
case: ([e1]_s) => p Hp.
case: ([e2]_s) => p2 Hp2.
rewrite phy_of_si32K /si32_of_phy /=.
case: (oi32_of_i8_Some _ Hp) => x Hx.
case: (oi32_of_i8_Some _ Hp2) => y Hy.
rewrite Hx Hy /=.
move: (oi32_of_i8_bij _ _ Hx) => ?; subst.
move: (oi32_of_i8_bij _ _ Hy) => ?; subst.
by rewrite !i8_of_i32K.
Opaque eval.
Qed.

Lemma phy_add_pe (t : g.-typ) (e1 : exp sigma (:* t)) (e2 : exp sigma (g.-ityp: sint)) :
  0 <=? s2Z (si32<=phy [ e2 ]_ s) ->
  ptr<=phy [ e1 \+ e2 ]_ s =
  ptr<=phy [ e1 ]_s `+ Z2u ptr_len (Z<=nat (sizeof t) * s2Z (si32<=phy [ e2 ]_ s)).
Proof.
Transparent eval.
move=> e2_pos /=.
move H1 : ([ e1 ]_ s) => [h1 Hh1].
move H2 : ([ e2 ]_ s) => [h2 Hh2].
have : size h1 = sizeof_ptr by rewrite Hh1 sizeof_ptyp.
case/optr_of_i8_Some => x1 Hx1.
have : size h2 = 4%nat by rewrite Hh2 sizeof_ityp.
case/oi32_of_i8_Some => x2 Hx2.
rewrite H2 /si32_of_phy /= Hx2 /= in e2_pos.
rewrite /add_prod (i32_of_i8_bij3 h2 x2) // e2_pos phy_of_ptrK.
by rewrite /ptr_of_phy /= Hx1 /= (optr_of_i8_bij3 _ x1) // /si32_of_phy /= Hx2.
Opaque eval.
Qed.

End eval_sect.

Notation "e '|le~>' val" :=
  (fun st hp => @log_mapsto _ _ val (Z.abs_nat (Z<=u (ptr<=phy ([ e ]_st)))) hp)
  (at level 77, no associativity) : C_expr_scope.

Notation "e '|pe~>' val" :=
  (fun st hp => @phy_mapsto _ _ val (Z.abs_nat (Z<=u (ptr<=phy ([ e ]_st)))) hp)
  (at level 77, no associativity) : C_expr_scope.

(** boolean expression *)

Inductive bexp {g} (sigma : g.-env) :=
| exp2bexp of exp sigma (g.-ityp: uint)
| bneg of bexp sigma.

Reserved Notation "'[' e ']b_' s" (at level 9).

Fixpoint beval {g} {sigma : g.-env} (e : bexp sigma) (s : store sigma) : bool :=
  match e with
    | exp2bexp e' => ~~ is_zero [ e' ]_ s
    | bneg e' => negb [ e' ]b_ s
  end
where "'[' e ']b_' s" := (beval e s) : C_expr_scope.
Global Opaque beval.

Notation "'\~b' b" := (bneg _ b) (at level 71, format "'['  \~b  b  ']'") : C_expr_scope. (* NB: logical negation, exists in C? *)

Notation "'\b' e" := (exp2bexp _ e) (at level 70, format "'['  \b  e  ']'") : C_expr_scope.

Fixpoint subst_bexp {g} {sigma : g.-env} x {t : g.-typ}
  (Hx : env_get x sigma = Some t) (e' : exp sigma t) (b : bexp sigma) : bexp sigma :=
  match b with
    | exp2bexp e => \b subst_exp x Hx e' e
    | bneg b => bneg _ (subst_bexp x Hx e' b)
  end.

Lemma subst_bexp_store_upd {g} {sigma : g.-env} (x : string) {t : g.-typ} {Hx : env_get x sigma = Some t} (e' : exp sigma t) s: forall (b : bexp sigma),
  [ subst_bexp x Hx e' b ]b_ s = [ b ]b_ (store_upd Hx ([ e' ]_ s) s).
Proof.
Transparent beval.
elim => /= [e | b Hind].
- by rewrite subst_exp_store_upd.
- by rewrite Hind.
Opaque beval.
Qed.

Fixpoint bvars {g} {sigma : g.-env} (b : bexp sigma) :=
  match b with
    | exp2bexp e => vars e
    | bneg b => bvars b
  end.

Lemma bvars_subset_sigma {g} {sigma : g.-env} :
  forall (b : bexp sigma), {subset bvars b <= sigma}.
Proof. elim => //=. exact vars_in_ts. Qed.

Lemma beval_store_upd_notin {g} sigma :
  forall (b : bexp sigma) (t : g.-typ) str (str_t : env_get str sigma = Some t) pv,
    str \notin unzip1 (bvars b) ->
    forall s, [ b ]b_ (store_upd str_t pv s) = [ b ]b_ s.
Proof.
Transparent beval.
elim => /= [e t str str_t pval Hnotin s | b Hind ty' str str_t pval Hnotin s].
- by rewrite eval_store_upd_notin.
- by rewrite Hind.
Opaque beval.
Qed.

Section beval_sect.

Variable (g : wfctxt) (sigma : g.-env) (s : store sigma).

Lemma one_uc : [ \b ([ 1 ]uc : exp sigma _) ]b_ s.
Proof.
Transparent beval eval.
by rewrite /= not_is_zero_1.
Opaque beval eval.
Qed.

Lemma beval_neg_not (b : bexp sigma) : [ \~b b ]b_ s = ~~ [ b ]b_ s.
Proof. by case b. Qed.

Lemma beval_eq_e_eq t (a b : exp sigma (ityp: t)) :
  [ \b a \= b ]b_ s = ([ a ]_ s == [ b ]_ s).
Proof.
Transparent eval beval.
case: t a b => //= a b; case: ([ a ]_ s) => ha Ha; case: ([ b ]_ s) => hb Hb.
- case: ifP => [ | / negbT H ].
    move/eqP/u2Z_inj/i32_of_i8_inj => ?; subst hb.
    rewrite not_is_zero_1.
    by apply/esym/eqP/mkPhy_irrelevance.
  rewrite is_zero_0; apply/esym/negbTE.
  move: H; apply contra.
  case/eqP => ?; subst ha.
  by rewrite (_ : Ha = Hb) //; apply/eq_irrelevance.
- case: ifP => [ | / negbT H ].
    move/eqP/s2Z_inj/i32_of_i8_inj => ?; subst hb.
    rewrite not_is_zero_1.
    by apply/esym/eqP/mkPhy_irrelevance.
  rewrite is_zero_0; apply/esym/negbTE.
  move: H; apply contra.
  case/eqP => ?; subst ha.
  by rewrite (_ : Ha = Hb) //; apply/eq_irrelevance.
- case: ifP => [ | / negbT H ].
    move/eqP/u2Z_inj/i8_to_i8_inj => ?; subst hb.
    rewrite not_is_zero_1.
    by apply/esym/eqP/mkPhy_irrelevance.
  rewrite is_zero_0; apply/esym/negbTE.
  move: H; apply contra.
  case/eqP => ?; subst ha.
  by rewrite (_ : Ha = Hb) //; apply/eq_irrelevance.
- case: ifP => [ | / negbT H ].
    move/eqP/s2Z_inj/i8_to_i8_inj => ?; subst hb.
    rewrite not_is_zero_1.
    by apply/esym/eqP/mkPhy_irrelevance.
  rewrite is_zero_0; apply/esym/negbTE.
  move: H; apply contra.
  case/eqP => ?; subst ha.
  by rewrite (_ : Ha = Hb) //; apply/eq_irrelevance.
- case: ifP => [ | / negbT H ].
    move/eqP/u2Z_inj/i64_of_i8_inj => ?; subst hb.
    rewrite not_is_zero_1.
    by apply/esym/eqP/mkPhy_irrelevance.
  rewrite is_zero_0; apply/esym/negbTE.
  move: H; apply contra.
  case/eqP => ?; subst ha.
  by rewrite (_ : Ha = Hb) //; apply/eq_irrelevance.
Opaque eval beval.
Qed.

Lemma beval_neq_not_bneg (t : integral) (a b : exp sigma (ityp: t)) :
 [ \b a \!= b  ]b_ s = [ \~b \b a \= b ]b_ s.
Proof.
Transparent eval beval.
rewrite /= negbK.
move Ha : ( [ a ]_s ) => [ha Hha].
move Hb : ( [ b ]_s ) => [hb Hhb].
case: t a b Hha Ha Hhb Hb => a b Hha _ Hhb _; case: ifP => //= ?.
- rewrite is_zero_0.
  apply/esym/negbTE => /=.
  by rewrite not_is_zero_1.
  by rewrite is_zero_0 not_is_zero_1.
- rewrite is_zero_0.
  apply/esym/negbTE => /=.
  by rewrite not_is_zero_1.
  by rewrite is_zero_0 not_is_zero_1.
- rewrite is_zero_0.
  apply/esym/negbTE => /=.
  by rewrite not_is_zero_1.
  by rewrite is_zero_0 not_is_zero_1.
- rewrite is_zero_0.
  apply/esym/negbTE => /=.
  by rewrite not_is_zero_1.
  by rewrite is_zero_0 not_is_zero_1.
- rewrite is_zero_0.
  apply/esym/negbTE => /=.
  by rewrite not_is_zero_1.
  by rewrite is_zero_0 not_is_zero_1.
Opaque eval beval.
Qed.

Lemma beval_neq_not_eq (t : integral) (a b : exp sigma (ityp: t)) :
  [ \b a \!= b  ]b_ s = ([ a ]_ s != [ b ]_ s).
Proof. by rewrite beval_neq_not_bneg beval_neg_not beval_eq_e_eq. Qed.

Lemma beval_eq_p_eq (t : g.-typ) (a b : exp sigma (:* t)) :
  [ \b a \= b ]b_ s = ([ a ]_ s == [ b ]_ s).
Proof.
Transparent eval beval.
rewrite /=.
case: ifP => H; by [rewrite not_is_zero_1 | rewrite is_zero_0].
Opaque eval beval.
Qed.

Lemma beval_bop_r_le_ge (e1 e2 : exp sigma (g.-ityp: sint)) :
  [ \b e1 \<= e2 ]b_ s -> [ \b e2 \>= e1 ]b_ s.
Proof.
Transparent eval beval.
rewrite /=.
move He1 : ( [ e1 ]_s ) => [? ?].
move He2 : ( [ e2 ]_s ) => [? ?].
by case: ifP.
Opaque eval beval.
Qed.

Lemma beval_bop_r_ge_le (e1 e2 : exp sigma (g.-ityp: sint)) :
  [ \b e1 \>= e2 ]b_ s -> [ \b e2 \<= e1 ]b_ s.
Proof.
Transparent eval beval.
rewrite /=.
move He1 : ( [ e1 ]_s ) => [? ?].
move He2 : ( [ e2 ]_s ) => [? ?].
by case: ifP.
Opaque eval beval.
Qed.

(* NB: see also Ceqpn_add2l in C_expr_equiv *)
Lemma Ceqpn_add2l' t (e : exp sigma (:* t)) e1 e2 :
  [ \b e1 \= e2 ]b_ s -> [ \b e \+ e1 \= e \+ e2 ]b_ s.
Proof.
Transparent beval eval.
rewrite /=.
move e1_v1 : ([ e1 ]_s) => [v1 Hv1].
move e2_v2 : ([ e2 ]_s) => [v2 Hv2].
move e_v : ([ e ]_s) => [v Hv].
case: ifP; last by rewrite is_zero_0.
move/eqP/s2Z_inj => -> _.
case: ifP; first by rewrite not_is_zero_1.
by rewrite eqxx.
Opaque beval eval.
Qed.

Lemma beval_land_e (e1 e2 : exp sigma (ityp: uint)) :
  [ \b e1 \&& e2 ]b_ s = [ \b e1 ]b_ s && [ \b e2 ]b_ s.
Proof.
Transparent beval eval.
move He1_s : ( [ e1 ]_ s ) => e1_pv.
destruct e1_pv as [e1_lst He1_lst].
have : size e1_lst = 4%nat by rewrite He1_lst sizeof_ityp.
case/oi32_of_i8_Some => e1_int He1_int.
move He2_s : ( [ e2 ]_ s ) => e2_pv.
destruct e2_pv as [e2_lst He2_lst].
have : size e2_lst = 4%nat by rewrite He2_lst sizeof_ityp.
case/oi32_of_i8_Some => e2_int He2_int.
- rewrite /= He1_s He2_s /is_zero.
  case: ifP.
  + case/orP.
    * move/eqP.
      rewrite {1}(_ : Z0 = u2Z (Z2u 32 0)); last by rewrite Z2uK.
      move/u2Z_inj/i32_of_i8_bij => ?; subst e1_lst.
      rewrite eq_refl /=.
      apply/esym/negbTE.
      rewrite negb_and /= 2!negbK.
      apply/orP; left.
      by apply/eqP/mkPhy_irrelevance.
    * move/eqP.
      rewrite {1}(_ : Z0 = u2Z (Z2u 32 0)); last by rewrite Z2uK.
      move/u2Z_inj/i32_of_i8_bij => ?; subst e2_lst.
      rewrite eq_refl /=.
      apply/esym/negbTE.
      rewrite negb_and /= 2!negbK.
      apply/orP; right.
      by apply/eqP/mkPhy_irrelevance.
  + move/negbT; rewrite negb_or.
    move/andP.
    rewrite {1}(_ : Z0 = u2Z (Z2u 32 0)); last by rewrite Z2uK.
    rewrite {2}(_ : Z0 = u2Z (Z2u 32 0)); last by rewrite Z2uK.
    case=> /eqP He1 /eqP He2.
    rewrite not_is_zero_1.
    apply/esym/andP; split.
    * apply/negP. case/eqP => ?; subst e1_lst.
      by rewrite i8_of_i32K in He1.
    * apply/negP. case/eqP => ?; subst e2_lst.
      by rewrite i8_of_i32K in He2.
Opaque beval eval.
Qed.

Lemma beval_le0_or_e (e1 e2 : exp sigma (ityp: sint)) :
  [ \b [ 0 ]sc \<= e1 ]b_ s && [ \b [ 0 ]sc \<= e2 ]b_ s -> [ \b [ 0 ]sc \<= (e1 \| e2) ]b_ s.
Proof.
Transparent eval beval.
rewrite /=.
move H1 : ([ e1 ]_s) => [h1 Hh1].
move H2 : ([ e2 ]_s) => [h2 Hh2].
rewrite i8_of_i32K.
have Hh1' : size h1 = 4%nat by rewrite Hh1 sizeof_ityp.
have Hh2' : size h2 = 4%nat by rewrite Hh2 sizeof_ityp.
have -> : eq_ind_r (fun t => size h1 = sizeof (ityp: t)) Hh1 erefl = Hh1'.
  by apply eq_irrelevance.
have -> : eq_ind_r (fun t => size h2 = sizeof (ityp: t)) Hh2 erefl = Hh2'.
  by apply eq_irrelevance.
rewrite Z2sK //.
case/andP.
case: ifP => [Ha _ | ]; last by rewrite is_zero_0.
case: ifP => [Hb _ | ]; last by rewrite is_zero_0.
rewrite {1}/phy_of_int_nosimpl /= 2!i8_of_i32K Z2sK //.
case: ifP; first by rewrite not_is_zero_1.
move/negbT.
by rewrite (le0_or Ha Hb).
Opaque eval beval.
Qed.

Lemma beval_uchar0 (e : exp sigma (ityp: uchar)) : [ \b [ 0 ]sc \<= (int) e ]b_ s.
Proof.
Transparent eval beval.
rewrite /= /safe_cast_phy_uchar.
move H : ( [ e ]_s ) => [h Hh].
have Hh' : size h = 1%nat by rewrite Hh sizeof_ityp.
destruct h as [ | h [|] ] => //.
by rewrite i8_of_i32K Z2sK // i8_of_i32K (s2Z_zext (8 * (4 - 1))) // min_u2Zb not_is_zero_1.
Opaque eval beval.
Qed.

Lemma beval_shl_uchar0 (e : exp sigma (ityp: uchar)) :
  [ \b [ 0 ]sc \<= (int) e \<< [ 8 ]sc ]b_ s.
Proof.
Transparent eval beval.
rewrite /= /safe_cast_phy_uchar.
move H : ( [ e ]_s ) => [h Hh].
have Hh' : size h = 1%nat by rewrite Hh sizeof_ityp.
destruct h as [ | h [|] ] => //.
rewrite 2!i8_of_i32K -s2Z_u2Z_pos; last by rewrite Z2sK.
rewrite Z2sK //= 2!i8_of_i32K Z2sK //= (@s2Z_shl 8) //; last first.
  rewrite (s2Z_zext (8 * (4 - 1))) //.
  split; last exact: max_u2Z.
  apply (@leZ_trans Z0) => //; exact: min_u2Z.
rewrite (s2Z_zext (8 * (4 - 1))) //.
case: ifP; first by rewrite not_is_zero_1.
move/negbT.
rewrite -Z.ltb_antisym.
move/ltZP.
case/Zlt_mult_0_inv.
  case => abs _.
  move: (min_u2Z h) => ?; lia.
by case.
Opaque eval beval.
Qed.

(* NB: useful? *)
Lemma beval_neq_e_sint (e1 e2 : exp sigma _) :
  [ \b e1 \!= e2 ]b_ s = (si32<=phy ([e1]_ s) != si32<=phy ([e2]_ s)).
Proof.
Transparent eval beval.
move H1 : ([ e1 ]_s) => [h1 Hh1].
move H2 : ([ e2 ]_s) => [h2 Hh2].
have Hh1' : size h1 = 4%nat by rewrite Hh1 sizeof_ityp.
have Hh2' : size h2 = 4%nat by rewrite Hh2 sizeof_ityp.
case/oi32_of_i8_Some : Hh1' => x Hx.
case/oi32_of_i8_Some : Hh2' => y Hy.
rewrite /= H1 H2.
case: ifP => H.
  rewrite /si32_of_phy /= Hx /= Hy /= is_zero_0 /=.
  apply/esym/eqP.
  move/eqP/s2Z_inj/i32_of_i8_inj : H => ?; subst.
  by rewrite Hy in Hx; case: Hx.
rewrite not_is_zero_1.
apply/esym.
move/negbT : H; apply contra => /eqP H.
rewrite /si32_of_phy /= Hx Hy /= in H; subst y.
move: (oi32_of_i8_inj _ _ _ Hx Hy) => ?; subst h2.
apply/eqP.
congr (Z<=s (i32<=i8 _ _)).
apply eq_irrelevance.
Opaque eval beval.
Qed.

Lemma bop_re_ge_Zge (e1 e2 : exp sigma (g.-ityp: _)) :
  [ \b e1 \>= e2 ]b_ s -> s2Z (si32<=phy [ e1 ]_s) >= s2Z (si32<=phy [ e2 ]_s).
Proof.
Transparent eval beval.
rewrite /=.
move He1 : ( [ e1 ]_s ) => [he1 Hhe1].
move He2 : ( [ e2 ]_s ) => [he2 Hhe2].
case: ifP; last by move=> _; rewrite /is_zero eqxx.
move/leZP => H _.
apply Z.le_ge.
set lhs := si32<=phy _.
set rhs := si32<=phy _.
set lhs2 := i32_of_i8 _ _ in H.
set rhs2 := i32_of_i8 _ _ in H.
have -> : lhs = lhs2.
  rewrite /lhs /lhs2 /si32_of_phy /=.
  have : size he2 = 4%nat by rewrite Hhe2 sizeof_ityp.
  case/oi32_of_i8_Some => x Hx; rewrite Hx /=.
  by apply/esym/i32_of_i8_bij2/oi32_of_i8_bij.
rewrite (_ : rhs = rhs2) // /rhs /rhs2 /si32_of_phy /=.
have : size he1 = 4%nat by rewrite Hhe1 sizeof_ityp.
case/oi32_of_i8_Some => x Hx; rewrite Hx /=.
by apply/esym/i32_of_i8_bij2/oi32_of_i8_bij.
Opaque eval beval.
Qed.

Lemma bop_re_le_Zle (e1 e2 : exp sigma (g.-ityp: _)) :
  [ \b e1 \<= e2 ]b_ s -> s2Z (si32<=phy [ e1 ]_s) <= s2Z (si32<=phy [ e2 ]_s).
Proof. move=> H. exact/Z.ge_le/bop_re_ge_Zge/beval_bop_r_le_ge. Qed.

Lemma bop_re_lt_Zlt (e1 e2 : exp sigma (g.-ityp: sint)) :
  [ \b e1 \< e2 ]b_ s -> s2Z (si32<=phy [ e1 ]_s) < s2Z (si32<=phy [ e2 ]_s).
Proof.
Transparent eval beval.
rewrite /=.
move He1 : ( [ e1 ]_s ) => [he1 Hhe1].
move He2 : ( [ e2 ]_s ) => [he2 Hhe2].
case: ifP; last by move=> _; rewrite /is_zero eqxx.
move/ltZP => H _.
set lhs := si32<=phy _.
set rhs := si32<=phy _.
set lhs1 := i32_of_i8 _ _ in H.
set rhs1 := i32_of_i8 _ _ in H.
have -> : lhs = lhs1.
  rewrite /lhs /lhs1 /si32_of_phy /=.
  have : size he1 = 4%nat by rewrite Hhe1 sizeof_ityp.
  case/oi32_of_i8_Some => x Hx; rewrite Hx /=.
  by apply/esym/i32_of_i8_bij2/oi32_of_i8_bij.
rewrite (_ : rhs = rhs1) // /rhs /rhs1 /si32_of_phy /=.
have : size he2 = 4%nat by rewrite Hhe2 sizeof_ityp.
case/oi32_of_i8_Some => x Hx; rewrite Hx /=.
by apply/esym/i32_of_i8_bij2/oi32_of_i8_bij.
Opaque eval beval.
Qed.

End beval_sect.

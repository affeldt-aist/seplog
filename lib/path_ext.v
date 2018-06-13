(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import path.

Set Implicit Arguments.
Unset Strict Implicit.

Section Type_ext.

Variable A : Type.

Lemma path_rel_inj (r1 r2 : rel A) :
  (forall from to, r1 from to = r2 from to) ->
  forall tl hd, path r1 hd tl = path r2 hd tl.
Proof.
move=> H; by elim => //= hd' tl -> hd; rewrite H.
Qed.

Lemma cycle_rel_inj (r1 r2 : rel A) :
  (forall from to, r1 from to = r2 from to) ->
  forall l, cycle r1 l = cycle r2 l.
Proof. move=> Heq [] //= hd tl; exact: path_rel_inj. Qed.

End Type_ext.

Section eqType_ext.

Variable A : eqType.

Lemma ucycle_rel_inj (r1 r2 : rel A) :
  (forall from to, r1 from to = r2 from to) ->
  forall l, ucycle r1 l = ucycle r2 l.
Proof.
move=> Heq [] //= hd tl.
by rewrite /ucycle (@cycle_rel_inj _ r1 r2).
Qed.

Lemma path_R_behead (P : pred A) (R : rel A) :
  (forall x y, R x y -> P y) ->
  forall tl hd, path R hd tl ->
  forall x, x \in tl -> P x.
Proof.
move=> HPR.
elim => //= t s Hind hd /andP [] HhdRt Hpath x.
rewrite in_cons => /orP[/eqP -> | Hin].
- exact: HPR _ _ HhdRt.
- exact: (Hind t).
Qed.

Lemma path_R_belast (P : pred A) (R : rel A) :
  (forall x y, R x y -> P x) ->
  forall hd tl, path R hd tl ->
  forall x, x \in belast hd tl -> P x.
Proof.
move=> HPR hd.
apply: last_ind => //= s x Hs.
rewrite rcons_path => /andP[HPaths Hlast].
move: {Hs}(Hs HPaths) => Hin.
move=> i.
rewrite belast_rcons in_cons => /orP[/eqP ->|].
- case: s HPaths Hlast Hin => //= [ _ HhdRx _ | hd' tl] .
  + exact: HPR HhdRx.
  + move => /andP[HhdRhd' _] _ _.
    exact: HPR HhdRhd'.
- case: (lastP s) Hlast Hin => //= s0 x0.
  rewrite last_rcons => HR Hbelast.
  rewrite mem_rcons in_cons => /orP[/eqP ->|Hin].
  - exact: (HPR _ _ HR).
  - apply: Hbelast.
    by rewrite belast_rcons in_cons Hin orbT.
Qed.

End eqType_ext.

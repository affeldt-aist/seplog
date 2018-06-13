(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Program.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import div path tuple.
Require Import Init_ext String_ext ssrnat_ext Max_ext seq_ext.
Require Import tuple_ext path_ext finmap.
Require order.

Local Close Scope Z_scope.

(** * C types *)

(** tags for C struct *)

Inductive tag := mkTag : string -> tag.

Definition eq_tag t1 t2 := match t1, t2 with mkTag s1, mkTag s2 => s1 == s2 end.

Lemma eq_tagP : Equality.axiom eq_tag.
Proof.
move=> [x] [y]; apply: (iffP idP).
rewrite /eq_tag; by move/eqP => ->.
case=> ->; by apply/eqP.
Qed.

Canonical Structure tag_eqMixin := EqMixin eq_tagP.
Canonical Structure tag_eqType := Eval hnf in EqType _ tag_eqMixin.

Module TagOrder <: order.ORDER.

Definition A : eqType := tag_eqType.

Definition ltA (a b : A) : bool :=
  match a, b with mkTag a, mkTag b => order.StringOrder.ltA a b end.

Lemma ltA_trans : forall n m p, ltA m n -> ltA n p -> ltA m p.
Proof. move=> [] ? [] ? [] ?; by apply order.StringOrder.ltA_trans. Qed.

Lemma ltA_total : forall m n, (m != n) = (ltA m n) || (ltA n m).
Proof. move=> [] ? [] ?. by rewrite /= -order.StringOrder.ltA_total. Qed.

Lemma ltA_irr : forall a, ltA a a = false.
Proof. move=> [] ?. by apply order.StringOrder.ltA_irr. Qed.

End TagOrder.

(** integral types: unsigned/signed integers, unsigned chars,
    unsigned long integers *)

Inductive integral : Set := uint | sint | uchar | schar | ulong.

Inductive typ : Set := ityp of integral | ptyp of typ | styp of tag
| atyp : forall sz, sz > 0 -> tag -> typ.

(** collect structure tags: *)

Fixpoint tags t : seq tag :=
  match t with
    | ityp _ => nil
    | ptyp t' => tags t'
    | styp tg => tg :: nil
    | atyp _ _ tg => tg :: nil
  end.

Lemma incl_tags_ptyp_inv : forall t (l : seq tag),
  {subset (tags (ptyp t)) <= l} -> {subset (tags t) <= l}.
Proof. by case. Qed.

Definition eqit (t1 t2 : integral) : bool :=
  match t1, t2 with
    | uint, uint => true
    | sint, sint => true
    | uchar, uchar => true
    | schar, schar => true
    | ulong, ulong => true
    | _, _ => false
  end.

Lemma eqit_inj : forall t1 t2, eqit t1 t2 -> t1 = t2.
Proof. by move=> [] []. Qed.

Lemma eqit_refl : forall (t : integral), eqit t t.
Proof. by move=> []. Qed.

Lemma eqitP : Equality.axiom eqit.
Proof.
move=> x y.
apply: (iffP idP).
by move/eqit_inj.
move=> ->; by apply eqit_refl.
Qed.

Canonical Structure ityp_eqMixin := EqMixin eqitP.
Canonical Structure ityp_eqType := Eval hnf in EqType _ ityp_eqMixin.

(** a relation between types that does not behave yet as an equality
   (refl and sym only) (eqtm will behave as an equality) *)

Fixpoint eqt t1 t2 : bool :=
  match t1, t2 with
    | ityp it1   , ityp it2    => eqit it1 it2
    | ptyp a     , ptyp b      => eqt a b
    | styp tg1   , styp tg2    => tg1 == tg2
    | atyp n1 _ tg1, atyp n2 _ tg2 => (n1 == n2) && (tg1 == tg2)
    | _          , _           => false
  end.

Notation "t1 '=t=' t2" := (eqt t1 t2) (at level 50) : C_types_scope.

Local Open Scope C_types_scope.

Lemma eqt_inj : forall t1 t2, t1 =t= t2 -> t1 = t2.
Proof.
elim => [ | t IH | tg | n Hn tg ].
- move=> i [] //= i2; by move/eqit_inj ->.
- case=> // t' /=; by move/IH => <-.
- case=> // tg' /=; by move/eqP => <-.
- case => // n' Hn' tg' /= /andP [] /eqP => Heq1 /eqP Heq2; subst.
  by have ->: Hn = Hn' by apply/eq_irrelevance.
Qed.

Lemma eqt_refl : forall t, t =t= t.
Proof.
elim => [ | | tg | n Hn tg].
- exact eqit_refl.
- by move=> [] t_t.
- rewrite /eqt /=; by apply/eqP.
- by rewrite /eqt /= !eq_refl.
Qed.

Lemma eqt_sym a b : a =t= b -> b =t= a.
Proof. move/eqt_inj => <-; by apply eqt_refl. Qed.

(** build the eqType of typ: *)

Lemma eqtP : Equality.axiom eqt.
Proof.
move=> x y.
apply: (iffP idP).
by move/eqt_inj.
move=> ->; by apply eqt_refl.
Qed.

Canonical Structure typ_eqMixin := EqMixin eqtP.
Canonical Structure typ_eqType := Eval hnf in EqType _ typ_eqMixin.

(** padding: *)

Definition padd addr ali :=
  let r := addr %% ali in
    if r == 0 then 0 else ali - r.

Eval compute in (1 + (padd 1 4)).
Eval compute in (2 + (padd 2 4)).
Eval compute in (3 + (padd 3 4)).
Eval compute in (4 + (padd 4 4)).
Eval compute in (padd 0 4).

Lemma padd0n n: padd 0 n = 0.
Proof. by case: n. Qed.

Lemma padd_max addr align : align > 0 -> (padd addr align < align)%nat.
Proof.
move=> Halign.
rewrite /padd.
case: posnP => Heq //.
rewrite -[X in _ < X]subn0.
by rewrite ltn_sub2l.
Qed.

Lemma padd_0 addr align : align > 0 -> align %| addr -> padd addr align = O.
Proof.
move => Halign Hdiv.
rewrite /padd.
case: posnP => //.
rewrite (@dvdn_eq align addr) in Hdiv.
move/eqP in Hdiv.
by rewrite -Hdiv modnMl.
Qed.

Lemma padd_idempotent addr align: align > O -> align %| addr -> padd (addr + padd addr align) align = O.
Proof.
move=> Halign Hdiv.
by rewrite (padd_0 addr align) // addn0 padd_0.
Qed.

Lemma padd_isdiv : forall addr ali,  ali > 0 -> ali %| addr + padd addr ali.
Proof.
rewrite /padd => addr ali Hali.
case: posnP => Hmod.
- rewrite addnC add0n.
  by move/eqP: Hmod.
- rewrite addnBA; last first.
    + apply ltnW.
      rewrite ltn_pmod //.
    + rewrite modn_def.
      case: edivnP => q r /= -> _.
      by rewrite addnC !addnA -addnBA // subnn addn0 -{2}(mul1n ali) -mulnDl dvdn_mull.
Qed.

Lemma padd_add : forall a t b, t %| a -> padd (a + b) t = padd b t.
Proof.
case=> // a t b ta.
rewrite /padd.
case/orP : (orbN (t %| b)) => tb.
- have H2 : b %% t == O = true.
    case/dvdnP : tb => kb ->.
    by rewrite modnMl.
  have -> : (a.+1 + b) %% t == O = true.
    case/dvdnP : ta => ka ->.
    by rewrite modnMDl.
  by rewrite H2.
- have H2 : b %% t == O = false.
    apply/negbTE.
    move: tb; apply contra => tb.
    rewrite dvdn_eq {2}(divn_eq b t).
    move/eqP in tb.
    by rewrite tb addn0.
  have -> : (a.+1 + b) %% t == O = false.
    case/dvdnP : ta => ka ->.
    by rewrite modnMDl.
  rewrite H2.
  rewrite -modnDml.
  case/dvdnP : ta => ka ->.
  by rewrite modnMl add0n.
Qed.

Lemma padd_sub a b t : t %| b -> b <= a -> padd (a - b) t = padd a t.
Proof.
move=> tb ba.
rewrite /padd.
case/orP : (orbN (t %| a)) => ta.
- have H2 : a %% t == O = true.
    case/dvdnP : ta => ka ->.
    by rewrite modnMl.
  rewrite H2 (_ : (a - b) %% t == O = true) //.
  case/dvdnP : ta => ka ->.
  case/dvdnP : tb => kb ->.
  by rewrite -mulnBl modnMl.
- have H2 : a %% t == O = false.
    apply/negbTE.
    move: ta; apply contra; move/eqP => ta.
    rewrite dvdn_eq {2}(divn_eq a t).
    by rewrite ta addn0.
  have -> : (a - b) %% t == O = false.
    apply/eqP/eqP.
    move/eqP/eqP : H2; apply contra => /eqP H2.
    apply/eqP.
    rewrite -H2.
    case/dvdnP : tb => kb Hkb.
    by rewrite Hkb mulnC modn_subr_eq // mulnC -Hkb.
  rewrite H2.
  congr (_ - _).
  case/dvdnP : tb => kb Hkb.
  by rewrite Hkb mulnC modn_subr_eq // mulnC -Hkb.
Qed.

(** a type context maps a tag with a list of "field/type"'s *)

Module Fields <: finmap.EQTYPE.
Definition A := [eqType of seq (string * typ)].
End Fields.

Module Ctxt := compmap TagOrder Fields.

Notation "a '|>' b '\,' c" :=
  (Ctxt.add (mkTag a) b c) (at level 69, b at next level, right associativity) : C_types_scope.
Notation "\O" := (Ctxt.emp) : C_types_scope.

(** first property of a type context: the completness;
   it means that all the structure typs in the codomain are also in the domain *)

Definition complete g :=
 forall tg flds, Ctxt.get tg g = |_ flds _| ->
  forall t, t \in unzip2 flds -> forall tg', tg' \in tags t ->
   exists flds', Ctxt.get tg' g = |_ flds' _|.

(** procedure by reflection for completness of type context *)

(* computation of the tags used in codomain of the context *)
Definition ctxt_codomain_tags (g : Ctxt.t) :=
  flatten (map tags (unzip2 (flatten (Ctxt.cdom g)))).

Lemma in_codomain {g : Ctxt.t} {n} {w} :
  Ctxt.get n g = Some w ->
  forall t,
    t \in unzip2 w ->
    forall tg,
      tg \in tags t ->
      tg \in ctxt_codomain_tags g.
Proof.
move=> Hin t Ht tg Htg.
rewrite /ctxt_codomain_tags.
have Hw : w \in Ctxt.cdom g by apply (Ctxt.get_Some_in_cdom _ n).
move: (in_flatten Ht Hw).
move/(in_flatten Htg).
by rewrite flatten_map.
Qed.

Definition completeb g := inc (ctxt_codomain_tags g) (Ctxt.dom g).

Lemma completeb_sound g : completeb g -> complete g.
Proof.
rewrite /completeb /complete.
move/incP' => Hsubset n w Hget t Ht tg Htg.
move: (in_codomain Hget _ Ht _ Htg) => Hin_codomain.
by apply Ctxt.in_dom_get_Some, Hsubset.
Qed.

(** another property of context: there is no cylcing definitions;
   this means that a structure does not contains itself as a sub-structure *)

(* for this we define the path of sub-structures (paths with the "is sub-structure" relation) *)

Definition nested g tg1 tg2 :=
  if Ctxt.get tg1 g is |_ l _| then
    has (fun x => match x.2 with
                | styp tg => tg2 == tg
                | atyp _ _ tg => tg2 == tg
                | _ => false
                  end) l
  else
    false.

Lemma nested_lhs_in_ctxt g from to : nested g from to -> from \in Ctxt.dom g.
Proof.
rewrite /nested.
move: (Ctxt.get from g) (Ctxt.get_Some_in_dom g from) => [] //= a HNext _.
exact: (HNext a).
Qed.

Module PathNested.

Record t g n : Type := mkt {
  p :> {:n.+1.-tuple tag} ;
  Hp1 : thead p \in Ctxt.dom g ;
  Hp : path (nested g) (thead p) (behead p) }.

End PathNested.

Coercion path_nested_coersion := PathNested.p.

Lemma path_nested_0_eq {g : Ctxt.t} s : forall
  (p : {p : PathNested.t g 0 | tlast p = s})
  (p': {p : PathNested.t g 0 | tlast p = s}),
  p = p'.
Proof.
move => [] [] //=.
case/tupleP => p p0 Hp1 Hp2 Hp3.
move => [] [] //=.
case/tupleP => p' p'0 Hp'1 Hp'2 Hp'3.
have ? : p = p'.
  move: (tuple0 p0) => Heq; simpl in Heq; subst p0.
  move: (tuple0 p'0) => Heq; simpl in Heq; subst p'0.
  rewrite /tlast //= theadE in Hp3.
  rewrite /tlast //= theadE in Hp'3.
  by subst p p'.
subst p'.
have ? : p0 = p'0 by rewrite (tuple0 p0) (tuple0 p'0).
subst p'0.
have ? : Hp'1 = Hp1 by apply eq_irrelevance.
subst Hp'1.
have ? : Hp'2 = Hp2 by apply eq_irrelevance.
subst Hp'2.
have ? : Hp'3 = Hp3 by apply eq_irrelevance.
by subst Hp'3.
Qed.

(* we can compute the set of all the nested_paths of length n *)

Definition all_are_nestedpaths g (n : nat) (s : seq {:n.+1.-tuple tag}) : Prop :=
  forall x, x \in s -> exists p : PathNested.t g n, x = p.

Definition all_nestedpaths_in g n (s : seq {:n.+1.-tuple tag}) :=
  forall (p : PathNested.t g n), PathNested.p _ _ p \in s.

(* compute all to in relation with a from w.r.t. nested *)
Definition compute_nested (g : Ctxt.t) (x : Ctxt.l) : seq Ctxt.l :=
  match Ctxt.get x g with
    | None => nil
    | Some flds =>
      foldl
        (fun acc x =>
           match x.2 with styp tg => tg :: acc | atyp _ _ tg => tg :: acc | _ => acc end)
        nil flds
  end.

Lemma nested_is_compute_nested g from to :
  (nested g from to) = (to \in compute_nested g from).
Proof.
rewrite /nested /compute_nested.
case: (Ctxt.get from g) => //=.
elim => //= hd tl Hind.
rewrite Hind.
set f := fun (acc : seq tag) (x : string * typ) => _.
have H : forall a b, foldl f (a ++ b) tl = foldl f a tl ++ b.
  clear.
  elim: tl => // h t IH a b /=.
  have -> : f (a ++ b) h = f a h ++ b.
    rewrite /f.
    by destruct h.2.
  by rewrite IH.
destruct hd.2 as [ | | | ] => //=.
by rewrite (H [::] [:: t]) mem_cat in_cons /= in_nil orbC /= orbF.
by rewrite (H [::] [:: t]) mem_cat in_cons /= in_nil orbC /= orbF.
Qed.

(* computation of the set of paths of size 0 *)
Definition one_paths (g : Ctxt.t) : seq {: 1.-tuple tag} :=
  map (fun hd => [tuple of hd :: nil]) (Ctxt.dom g).

(* NB: not used anywhere? *)
Lemma one_paths_sound g : all_are_nestedpaths g 0 (one_paths g).
Proof.
rewrite /all_are_nestedpaths /one_paths => //=.
move => x Hx.
suff Hx' : (thead x \in Ctxt.dom g) /\ path (nested g) (thead x) (behead x).
  by exists (PathNested.mkt _ _ x (proj1 Hx') (proj2 Hx')).
rewrite behead_tuple1 //=.
split=> //.
by move/mapP: Hx => [] x0 Hx0 ->.
Qed.

Lemma one_paths_complete g : all_nestedpaths_in g 0 (one_paths g).
Proof.
rewrite /all_nestedpaths_in /one_paths => //=.
case=> p //= Hin _.
apply/mapP.
exists (thead p) => //=.
by rewrite thead_tuple1.
Qed.

Lemma thead_belast_in_dom n g : forall (p : PathNested.t g n.+1),
  thead (tbelast p) \in Ctxt.dom g.
Proof. move => [] p //= Hin Hpath; by rewrite thead_tbelast. Qed.

Lemma path_tbelast n g : forall (p : PathNested.t g n.+1),
  let p' := tbelast p in
  path (nested g) (thead p') (behead p').
Proof.
move => [] p //= Hin Hpath.
rewrite -decomp_tuple -drop1 /= drop0 rcons_path in Hpath.
move/andP : Hpath => [] Hpath Hnext.
by rewrite /tlast thead_tbelast.
Qed.

Definition path_nested_belast {n} {g} (p : PathNested.t g n.+1) : PathNested.t g n.
apply (PathNested.mkt _ _ (tbelast p)).
apply thead_belast_in_dom.
apply path_tbelast.
Defined.

Lemma nested_tlast n g : forall (p : PathNested.t g n.+1),
  nested g (tlast (tbelast p)) (tlast p).
Proof.
case=> p //= Hin Hpath.
rewrite -decomp_tuple -drop1 /= drop0 rcons_path in Hpath.
move/andP: Hpath => [] _ HNext.
by rewrite /tlast thead_tbelast.
Qed.

Definition inc_path {n} (g : Ctxt.t) (t : {:n.+1.-tuple tag}) : seq {:n.+2.-tuple tag} :=
  let nexts := compute_nested g (tlast t) in
  map (trcons t) nexts.

Lemma inc_path_complete n g (p : PathNested.t g n.+1) :
  PathNested.p _ _ p \in inc_path g (tbelast p).
Proof.
apply/mapP.
exists (tlast p); last first.
  by rewrite trcons_tbelast_tlast.
by rewrite -nested_is_compute_nested nested_tlast.
Qed.

Lemma inc_path_sound {n g} (p : PathNested.t g n) : all_are_nestedpaths g n.+1 (inc_path g p).
Proof.
move => x Hx.
suff: (thead x \in Ctxt.dom g) /\ path (nested g) (thead x) (behead x).
  move: Hx => _ Hx.
  by exists (PathNested.mkt _ _ x (proj1 Hx) (proj2 Hx)).
rewrite /inc_path in Hx; move: Hx.
move/mapP => [] x0.
rewrite -nested_is_compute_nested => Hin ->.
rewrite thead_trcons.
split.
- exact: (PathNested.Hp1 _ _ p).
- rewrite behead_trcons // rcons_path.
  apply/andP; split.
  + exact: (PathNested.Hp _ _ p).
  + exact Hin.
Qed.

Definition inc_paths {n} (g : Ctxt.t) (s : seq {:n.+1.-tuple tag}) : seq {:n.+2.-tuple tag} :=
  flatten (map (fun hd => inc_path g hd) s).

Lemma inc_paths_complete g n s :
  all_nestedpaths_in g n s -> all_nestedpaths_in g n.+1 (inc_paths g s).
Proof.
move=> Hin p.
rewrite /all_nestedpaths_in in Hin.
rewrite /inc_paths.
move: (inc_path_complete n g p) => H.
have Hin' : PathNested.p _ _ (path_nested_belast p) \in s by apply Hin.
rewrite /inc_paths.
eapply in_flatten; last exact/Hin'.
exact/inc_path_complete.
Qed.

Lemma inc_paths_sound g n s :
  all_are_nestedpaths g n s -> all_are_nestedpaths g n.+1 (inc_paths g s).
Proof.
move => Hexists x.
rewrite /inc_paths.
move/flatten_in => [] x' [] Hx'1 Hx'2.
move: {Hexists Hx'2}(Hexists x' Hx'2) => [] p Hp.
subst x'.
apply (inc_path_sound p x Hx'1).
Qed.

Fixpoint compute_paths (g : Ctxt.t) n : seq {:n.+1.-tuple tag} :=
  match n with
    | 0 => one_paths g
    | S n => flatten (map (inc_path g) (compute_paths g n))
  end.

Lemma compute_paths_complete g n :
  all_nestedpaths_in g n (compute_paths g n).
Proof.
elim: n => [ | n].
- by apply one_paths_complete.
- by apply inc_paths_complete.
Qed.

Lemma compute_paths_empty g n : compute_paths g n = nil ->
  forall m, m >= n -> compute_paths g m = nil.
Proof.
move => Hn.
elim => [ | n0 IH].
  by rewrite leqn0 => /eqP <-.
rewrite leq_eqVlt.
case/orP.
- by move => /eqP <-; rewrite Hn.
- move=> /= n_n0; by rewrite IH.
Qed.

(* NB: rename to all_paths_uniq? *)
Definition no_cycle g := forall n (p : PathNested.t g n), uniq p.

Lemma uniq_path_size_ub g n : forall (p : PathNested.t g n),
  uniq p -> n <= size (Ctxt.dom g).
Proof.
case => p Hp1 Hp2 //= Huniq.
suff: size (tbelast p) <= (size (Ctxt.dom g)) by rewrite size_tuple.
apply uniq_leq_size => //=.
apply uniq_belast.
by rewrite (tuple_eta p) in Huniq.
rewrite /sub_mem => x Hxin .
by apply (path_R_belast (nested_lhs_in_ctxt g) Hp2).
Qed.

Lemma large_paths_not_uniq g n (p : PathNested.t g n) :
  n >= (size (Ctxt.dom g)).+1 ->  ~~ uniq p.
Proof.
rewrite leqNgt; apply contra; rewrite ltnS.
by apply uniq_path_size_ub.
Qed.

Definition no_cycleb g := compute_paths g (size (Ctxt.dom g)) == nil.

Lemma no_cycle_limit g :
  (forall n, n < size (Ctxt.dom g) -> forall (p : PathNested.t g n), uniq p) /\
  (forall n, n >= size (Ctxt.dom g) -> ~ (exists p : PathNested.t g n, True)) ->
  no_cycle g.
Proof.
case=> H1 H2 n p.
case/boolP : (size (Ctxt.dom g) <= n).
- move/H2; by case.
- rewrite -ltnNge.
  move/H1; by apply.
Qed.

Lemma uniqPn {A : eqType} (p : seq A) :
  reflect (exists p1 p2 p3 a, p1 ++ a :: p2 ++ a :: p3 = p) (~~ uniq p).
Proof.
apply: (iffP idP).
  elim: p => // h t IH /=.
  rewrite negb_and negbK.
  case/orP.
    case/splitPr => p1 p2.
    by exists (@nil A), p1, p2, h.
  case/IH => p1 [] p2 [] p3 [] h' <-.
  by exists (h :: p1), p2, p3, h'.
case=> p1 [] p2 [] p3 [] a <-.
by rewrite cat_uniq /= mem_cat inE eqxx /= orbT /= !andbF.
Qed.

Lemma loop_path (a : tag) p2 (e : rel tag) : forall n,
  cycle e (a :: p2) ->
  let it2 := fun acc => acc ++ a :: p2 in
  let loop := iter n.+1 it2 [::] in
  path e (head a loop) (behead loop).
Proof.
elim.
  rewrite /=.
  rewrite rcons_path.
  by case/andP.
move=> n IH /=.
rewrite rcons_path.
case/andP=> H1 H2.
rewrite /= in IH.
rewrite (_ : behead ((iter n (cat^~ (a :: p2)) [::] ++ a :: p2) ++ a :: p2) =
  behead (iter n (cat^~ (a :: p2)) [::] ++ a :: p2) ++ a :: p2); last first.
  clear.
  destruct n as [|n] => //=.
  rewrite -!drop1.
  rewrite drop_cat.
  by rewrite 2!size_cat addnC [size _]/= addSn addnA -(addnC (size
p2).+1) addSn /=.
rewrite (_ : head a ((iter n (cat^~ (a :: p2)) [::] ++ a :: p2) ++ a :: p2) =
  head a (iter n (cat^~ (a :: p2)) [::] ++ a :: p2)); last first.
  clear.
  destruct n as [|n] => //=.
  rewrite -2!nth0.
  by rewrite nth_cat size_cat addnC [size _]/= addSn /=.
rewrite cat_path.
rewrite IH /=; last by rewrite rcons_path H1 H2.
rewrite H1 andbC /=.
suff -> : last (head a (iter n (cat^~ (a :: p2)) [::] ++ a :: p2))
        (behead (iter n (cat^~ (a :: p2)) [::] ++ a :: p2)) = last a
p2 by assumption.
  clear.
  destruct n as [|n] => //.
  rewrite (_ : head a (iter (succn n) (cat^~ (a :: p2)) [::] ++ a ::
p2) = a); last first.
    elim: n a p2 => // n IH a p2.
    move: (IH a p2) => {IH}IH.
    rewrite iterS.
    rewrite -nth0 nth_cat size_cat addnC [size _]/= addSn /=.
    by rewrite -nth0 in IH.
  rewrite (_ : behead (iter (succn n) (cat^~ (a :: p2)) [::] ++ a :: p2) =
               behead (iter (succn n) (cat^~ (a :: p2)) [::]) ++ a ::
p2); last first.
    destruct n as [|n] => //=.
    rewrite -2!drop1.
    rewrite drop_cat.
    case: ifP => // abs.
    suff : false by done.
    rewrite -{}abs.
    rewrite size_cat addnC [size _]/= addSn.
    by rewrite size_cat addnA addnC [size _]/= addSn.
  by rewrite last_cat.
Qed.

Lemma no_cycleb_sound g : no_cycleb g -> no_cycle g.
Proof.
rewrite /no_cycleb.
move/eqP => H2.
apply no_cycle_limit.
split.
- move => n Hn p.
  apply/negPn/negP => H1.
  suff : exists m (p : PathNested.t g m),
           m >= size (Ctxt.dom g) /\
           (PathNested.p _ _ p \in compute_paths g m).
    case=> m [] p' [] K1 K2.
    move: (compute_paths_empty _ _ H2 _ K1) => abs.
    by rewrite abs in_nil in K2.
  case/uniqPn : H1 => p1 [] p2 [] p3 [] a H.
  have [q Hq] : exists q : PathNested.t g n, q = p.
    case: p H => /=; case=> p Hp K1 K2 H.
    simpl in *.
    subst p.
    eexists; reflexivity.
  pose it2 := fun acc => acc ++ a :: p2.
  pose loop := iter ((size (Ctxt.dom g)).+1) it2 nil.
  have [r Hr] : exists r : PathNested.t g (size loop).-1, loop = r.
    have [tloop Htloop] : exists tloop : (size loop).-tuple _, loop = tloop.
      have Hl : size loop == size loop by rewrite eqxx.
      by exists (Tuple Hl).
    have [k Hk] : exists k, size loop = k.+1.
      rewrite /loop /it2 /= size_cat /= addnC /= addSn; eexists; reflexivity.
    move: tloop Htloop.
    rewrite Hk /= => tloop Htloop.
    have Hlocal2 : forall x, x \in loop -> x \in a :: p2.
      rewrite /loop /it2 /=.
      move : (size (Ctxt.dom g)) => u.
      clear.
      elim: u => // u IH tg /=.
      rewrite mem_cat.
      case/orP => //.
      by apply IH.
    have ap2g : {subset (a :: p2) <= Ctxt.dom g}.
      move=> x Hx.
      case/(nthP a) : Hx => i Hi <-.
      apply nested_lhs_in_ctxt with (nth a (a :: p2 ++ a :: nil) i.+1).
      destruct q as [q K1 K2].
      destruct p as [p K3 K4].
      simpl in *.
      case: Hq => ?; subst p.
      move/pathP : K2.
      move/(_ a (size p1 + i)).
      have Htmp : size p1 + i < size (behead q).
        rewrite -H.
        destruct p1 as [|p1h p1d] => /=.
          rewrite add0n size_cat /=.
          rewrite addnS addnC -addnS.
          by apply ltn_addl.
        apply ltn_leq_trans with ((size p1d).+1 + (size p2).+1).
          by rewrite ltn_add2l.
        rewrite size_cat /= size_cat /=.
        nat_norm.
        by rewrite 2!ltnS leq_add2l leq_addr.
      move/(_ Htmp).
      suff : nth a (thead q :: behead q) (size p1 + i) = (nth a (a :: p2) i) /\
             (nth a (behead q) (size p1 + i)) = (nth a (p2 ++ [:: a]) i).
        by case=> -> ->.
      split.
        rewrite (_ : thead q :: behead q = q); last first.
          by rewrite [in X in _ = X](tuple_eta q).
        rewrite -H.
        rewrite nth_cat.
        rewrite (_ : size p1 + i < size p1 = false); last first.
          apply/negbTE.
          by rewrite -leqNgt leq_addr.
        rewrite addnC -addnBA // subnn addn0.
        by rewrite -cat_cons nth_cat /= Hi.
      rewrite -H nth_behead nth_cat.
      rewrite (_ : (size p1 + i).+1 < size p1 = false); last first.
        apply/negbTE.
        by rewrite -leqNgt -addnS leq_addr.
      rewrite -addnS addnC -addnBA // subnn addn0 /=.
      rewrite -cat1s catA nth_cat /=.
      by rewrite size_cat /= addnC Hi.
    have K1 : thead tloop \in Ctxt.dom g.
      apply ap2g.
      apply Hlocal2.
      by rewrite /thead /tnth -Htloop mem_nth // Hk.
    have K2 : path (nested g) (thead tloop) (behead tloop).
      rewrite -Htloop.
      rewrite (_ : thead tloop = head a loop); last first.
        rewrite Htloop.
        rewrite /thead /tnth -nth0.
        apply set_nth_default => //.
        by rewrite -Htloop Hk.
      apply loop_path.
      clear -Hq H.
      subst p.
      destruct q as [q K1q K2q].
      rewrite /= in H.
      rewrite -H in K2q.
      have {K2q}K2q : path (nested g) (last a p2) (a :: p2).
        rewrite /thead /tnth -H in K2q.
        rewrite nth0 in K2q.
        apply/(pathP a) => i /= Hi.
        rewrite ltnS in Hi.

        have Ktmp : (head (tnth_default q fintype.ord0) (p1 ++ a :: p2
++ a :: p3)
         :: behead (p1 ++ a :: p2 ++ a :: p3) = (p1 ++ a :: p2 ++ a :: p3)).
          rewrite -nth0.
          rewrite -drop1.
          rewrite -[X in _ = X](cat_take_drop 1).
          clear -p1.
          destruct p1 => /=; by rewrite drop0 take0.
        destruct i as [|i].
          simpl.
          move/(pathP a) : K2q.
          move/(_ (size p1 + (size p2))).
          set tmp := _ < _.
          have Htmp : tmp.
            rewrite /tmp {tmp}.
            rewrite size_behead size_cat /= addnS /= size_cat /= addnA.
            by rewrite -(addnC (size p3).+1) addSn ltnS leq_addl.
          move/(_ Htmp).
          rewrite Ktmp.
          rewrite nth_cat.
          case: ifP => Hcase.
            by rewrite -[X in _ < X]addn0 ltn_add2l ltn0 in Hcase.
          rewrite {1}addnC -addnBA // subnn addn0.
          rewrite -cat_cons nth_cat.
          case: ifP => Hcase'; last first.
            by rewrite /= ltnS leqnn in Hcase'.
          rewrite nth_last last_cons.
          rewrite catA -drop1.
          rewrite nth_drop.
          rewrite nth_cat.
          rewrite {1}size_cat [size (_ :: _)]/= addnS add1n ltnn.
          by rewrite size_cat [size (_ :: _)]/= addnS subnn.
        move/(pathP a) : K2q.
        move/(_ (size p1 + i)).
        set tmp := _ < _.
        have Htmp : tmp.
          rewrite /tmp {tmp}.
          rewrite size_behead size_cat /= addnS /=.
          rewrite ltn_add2l.
          rewrite size_cat.
          by apply ltn_addr.
        move/(_ Htmp).
        rewrite Ktmp.
        simpl.
        rewrite -{1}cat_cons.
        rewrite nth_cat.
        case: ifP => Hcase.
          by rewrite -[X in _ < X](addn0) ltn_add2l ltn0 in Hcase.
        rewrite {1}addnC -addnBA // subnn addn0.
        rewrite nth_cat.
        rewrite [size _]/=.
        rewrite ltnS.
        rewrite ltnW //.
        have -> : (nth a (behead (p1 ++ a :: p2 ++ a :: p3)) (size p1 + i)) =
                  (nth a p2 i).
          rewrite -drop1.
          rewrite nth_drop.
          rewrite addnC.
          rewrite -addnA.
          rewrite nth_cat.
          case: ifP => Hcase'.
            by rewrite -[X in _ < X](addn0) ltn_add2l ltn0 in Hcase'.
          rewrite addnC -addnBA // subnn addn0 addn1 /=.
          by rewrite nth_cat Hi.
        done.
      by rewrite (cycle_path a) last_cons.
    by exists (PathNested.mkt _ _ _ K1 K2).
  exists (predn (size loop)). exists r; split.
    rewrite /loop /it2.
    move : (size _) 0 nil => k u acc; clear.
    elim: k acc => //= k IH acc.
    rewrite size_cat addnC.
    set rhs := (X in _ < X).
    rewrite (_ : rhs = (rhs.-1.+1)); last first.
      rewrite prednK // /rhs.
      rewrite size_cat.
      rewrite -(addnC (size (_ :: _))) addnA [size _]/= addSn /=.
      by rewrite addnC addSn.
    rewrite ltnS.
    eapply leq_trans; first by apply (IH acc).
    rewrite /rhs.
    rewrite size_cat addnC addnA [size _]/= addnS addSn.
    rewrite succnK addSn.
    rewrite succnK 2!addSn.
    rewrite succnK -addnA.
    by apply leq_addl.
  by apply compute_paths_complete.
- move => n Hn [] Hex _.
  move: (compute_paths_complete _ _ Hex) => Hin.
  suff: compute_paths g n = nil by move=> Heq; rewrite Heq in Hin.
  by apply compute_paths_empty with (size (Ctxt.dom g)).
Qed.

Definition no_empty g := forall flds, flds \in Ctxt.cdom g -> size flds != 0.

Definition no_emptyb g := all (fun x => size x != 0) (Ctxt.cdom g).

Lemma no_emptyb_sound g : no_emptyb g -> no_empty g.
Proof.
rewrite /no_emptyb /no_empty.
move/allP; apply.
Qed.

(** context well formedness and sound decision procedure *)

Definition wf_ctxt g :=
  no_cycle g /\ complete g /\ no_empty g.

Lemma path_nested_uniq g (H : wf_ctxt g) n (p : PathNested.t g n ) :
  uniq p.
Proof. by apply (proj1 H n). Qed.

Definition wf_ctxtb g := no_cycleb g && completeb g && no_emptyb g.

Lemma wf_ctxtb_sound g : wf_ctxtb g -> wf_ctxt g.
Proof.
rewrite /wf_ctxtb /wf_ctxt.
move/andP => [] /andP [] Hnocycle Hcomplete Hnoempty.
split.
- by apply no_cycleb_sound.
split.
- by apply completeb_sound.
- by apply no_emptyb_sound.
Qed.

(** we create a sig type for well-formed contexts *)

Record wfctxt := mkWfctxt {
  wfctxtg :> Ctxt.t ;
  Hwfctxtg : wf_ctxt wfctxtg }.

Fixpoint topsort_tags t : seq tag :=
  match t with
    | ityp _ => nil
    | ptyp t' => nil
    | styp tg => tg :: nil
    | atyp _ _ tg => tg :: nil
  end.

Program Fixpoint topsort_ctxt_
  (sorted : seq (Ctxt.l * Ctxt.v)) (c : seq (Ctxt.l * Ctxt.v))
  {measure (size c)} :
  seq (Ctxt.l * Ctxt.v) :=
  let partp (p : Ctxt.l * Ctxt.v) :=
      all (fun t => has (fun p' => t == p'.1) sorted)
          (flatten [seq topsort_tags p'.2 | p' <- p.2]) in
  if filter partp c is [::]
    then sorted
    else topsort_ctxt_
           (sorted ++ (filter partp c))
           (filter (predC partp) c).
Next Obligation.
  apply/ltP; move: H.
  move/eqP.
  rewrite eq_sym -size_eq0 !size_filter.
  set partp := (fun p => all _ _).
  by rewrite -(count_predC partp c) -add1n leq_add2r lt0n.
Qed.

Definition topsort_ctxt (g : Ctxt.t) :=
  topsort_ctxt_ [::] (Ctxt.elts g).

Lemma in_path_in_dom : forall n (g : wfctxt) (p : PathNested.t g n),
  forall tg : tag, tg \in PathNested.p g n p -> tg \in Ctxt.dom g.
Proof.
elim => [g0 [p Hp Hp0] tg tg_p | n IH g0 [p Hp1 Hp] tg].
  simpl in tg_p.
  suff -> : tg = thead p by done.
  rewrite (tuple_eta p) inE in tg_p.
  case/orP : tg_p => [ /eqP // | ].
  by rewrite behead_tuple1 in_nil.
rewrite /= (tuple_eta p) inE.
case/orP => [ | tg_p]; first by move/eqP => ->.
apply: path_R_behead; last 2 first.
  by apply Hp.
  assumption.
move=> x y x_t /=.
rewrite /nested in x_t.
destruct g0 as [g1 [H1 [H2 H3]]] => /=.
simpl in Hp1, Hp, x_t.
rewrite /complete in H2.
move: x_t.
move HH : (Ctxt.get x g1) => [|] // hhh.
move: (H2 _ _ hhh) => {H2}H2.
case/hasP => x01 x02.
destruct x01 => //= Hs0.
have : s0 \in unzip2 HH by apply/mapP; exists (s, s0).
move/H2 => {H2}H2.
destruct s0 => //.
- move: (H2 t)                   .
  rewrite inE eqxx.
  case/(_ erefl) => x0.
  move/Ctxt.get_Some_in_dom => Htmp.
  move/eqP in Hs0.
  by subst t.
- move: (H2 t)                   .
  rewrite inE eqxx.
  case/(_ erefl) => x0.
  move/Ctxt.get_Some_in_dom => Htmp.
  move/eqP in Hs0.
  by subst t.
Qed.

Lemma wfctxt_is_complete (g : wfctxt) : complete g.
Proof. destruct g as [g Hg] => /=; red in Hg; tauto. Qed.

Lemma wfctxt_has_no_cycle (g : wfctxt) : no_cycle g.
Proof. destruct g as [g Hg] => /=; red in Hg; tauto. Qed.

Lemma wfctxt_has_no_empty (g : wfctxt) : no_empty g.
Proof. destruct g as [g Hg] => /=; red in Hg; tauto. Qed.

Lemma uniq_path_size_complete_ub (g : wfctxt) n (p : PathNested.t g n) :
  n < size (Ctxt.dom g).
Proof.
have Hcomplete : complete g by apply wfctxt_is_complete.
have Huniq : uniq p by move: (wfctxt_has_no_cycle g _ p).
case: p Huniq => p //=  Hp1 Hp2 Huniq.
suff: size p <= size (Ctxt.dom g) by rewrite size_tuple.
apply uniq_leq_size => //=.
move => x Hx.
have Hin: (forall from to, nested g from to -> to \in Ctxt.dom g).
- move => from to; rewrite /nested; move: {Hcomplete}(Hcomplete from).
  case: (Ctxt.get from g) => //= a Hcomplete.
  move/hasP => [] x0 Hx0 /eqP Hto.
  have Hin: x0.2 \in unzip2 a by apply/mapP; exists x0.
  move: {Hcomplete}(Hcomplete a (Logic.eq_refl _) x0.2 Hin to) => //=.
  destruct x0; simpl in *.
  destruct s0; simpl in * => //=.
  + move/eqP: Hto; move/eqP ->; rewrite inE (eq_refl _); move/(_ (Logic.eq_refl _)) => [] v Hv.
    by apply/(Ctxt.get_Some_in_dom _ _ v).
  + move/eqP: Hto; move/eqP ->; rewrite inE (eq_refl _); move/(_ (Logic.eq_refl _)) => [] v Hv.
    by apply/(Ctxt.get_Some_in_dom _ _ v).
move: Hx; rewrite (tuple_eta p); rewrite inE; move/orP => [].
- by move/eqP => ->.
- by move => H; apply (path_R_behead Hin Hp2).
Qed.

Notation "\wfctxt{ g \}" :=
  (mkWfctxt g (wf_ctxtb_sound g erefl)) (at level 50) : C_types_scope.

Lemma nested_rhs_in_wfctxt : forall (g : wfctxt) from to,
  nested g from to -> to \in Ctxt.dom g.
Proof.
move=> [] g [] Hg1 [] Hg2 Hg3 //= from to Hnext.
rewrite /nested in Hnext.
rewrite /complete in Hg2.
move: {Hg2}(Hg2 from) => Hg2.
destruct (Ctxt.get from g) => //=.
move/hasP: {Hnext}(Hnext) => [] x Hx1 Hx2.
move: {Hg2}(Hg2 s (Logic.eq_refl _) x.2) => Hg2.
have Hin: x.2 \in unzip2 s by apply/mapP; exists x; done.
move: {Hg2 Hin}(Hg2 Hin to) => Hg2.
move/eqP: Hx2 => Heq.
destruct x; simpl in Heq.
by destruct s1; simpl in Hg2 => //=; move/eqP: Heq => /eqP Heq; subst to; rewrite in_cons in_nil orbF in Hg2; move: {Hg2}(Hg2 (eq_refl _)) =>  [] y Hy; apply Ctxt.get_Some_in_dom with y.
Qed.

(** Definition of types covered by a context *)

Definition cover (g : Ctxt.t) (ty : typ) := inc (tags ty) (Ctxt.dom g).

Lemma in_dom_cover : forall (g0 : wfctxt) tg, tg \in Ctxt.dom g0 -> cover g0 (styp tg).
Proof.
case => g0 [H1 [H2 H3]] tg /= Htg.
case/Ctxt.in_dom_get_Some : Htg => x Htg.
rewrite /cover /=.
case: ifP => //.
move/negP.
by apply Ctxt.get_Some_in_dom in Htg.
Qed.

Definition Nexts_0 {g : Ctxt.t} : forall (tg : {s | cover g (styp s)}),
  {p : PathNested.t g 0 | tlast p = sval tg}.
move => s.
set v := [tuple (sval s)].
have Hv : (thead v \in Ctxt.dom g) /\ path (nested g) (thead v) (behead v).
  subst v => //=.
  split => //.
  rewrite theadE //=.
  destruct s as [x i] => /=.
  rewrite /cover in i.
  move/incP': i; apply.
  by rewrite in_cons //= in_nil orbC eqxx.
have Hv': tlast v = sval s.
subst v => //=.
exists (PathNested.mkt _ _ v (proj1 Hv) (proj2 Hv)).
reflexivity.
Defined.

Lemma behead_path_nested {g : wfctxt} : forall diff {n} {s : {s : tag | cover g (styp s)} }
  (p : {p : PathNested.t g n | tlast p = sval s}),
  {p : PathNested.t g (n - diff) | tlast p = sval s}.
Proof.
elim => /= [n p | diff Hind n s p].
- by rewrite subn0.
- case: (ltnP diff n) => Hndiff; last first.
  + have Heq1 : n - diff = 0 by apply/eqP; rewrite subn_eq0.
    have -> : n - diff.+1 = 0 by apply/eqP; rewrite subn_eq0; apply leqW.
    by apply Nexts_0.
  + have HS : n - diff = S (n - diff.+1) by rewrite -subnSK.
    move: {Hind}(Hind _ _ p) => p'.
    rewrite HS in p'; clear HS p.
    case: p' => x e.
    destruct x as [p Hp1 Hp].
    simpl in *.
    move: p Hp1 Hp e.
    case/tupleP => s1.
    case/tupleP  => s2 t /=.
    rewrite theadE => Hx1.
    rewrite tlastE.
    move/andP => [] Hx2 Hx3 Hx4.
    set p := [tuple of s2 :: t].
    have Hp : (thead p \in Ctxt.dom g) /\ path (nested g) (thead p) (behead p).
      split => //.
      rewrite/p; rewrite theadE.
      by apply nested_rhs_in_wfctxt with s1.
    by exists (PathNested.mkt _ _ p (proj1 Hp) (proj2 Hp)).
Qed.

Lemma wfctxt_get (g : wfctxt) n l : Ctxt.get n g = Some l ->
  forall x, x \in l -> cover g x.2.
Proof.
move=> Hget x Hx.
move: (wfctxt_is_complete g) => Hcomplete.
have Hunzip2: x.2 \in unzip2 l by apply/mapP; exists x.
apply/incP' => x' Hx'.
move/(Hcomplete _ _ Hget x.2 Hunzip2) : Hx' => [] ss Hss.
by apply/(Ctxt.get_Some_in_dom _ _ ss).
Qed.

Lemma wfctxt_get2 (g : wfctxt) : forall n l, Ctxt.get n g = Some l ->
  forall x, x \in unzip2 l -> cover g x.
Proof.
move => n l Hget x Hx.
move: (wfctxt_is_complete g) => Hcomplete.
apply/incP'  => x' Hx'.
move: {Hcomplete}(Hcomplete _ _ Hget x Hx x' Hx') => [] ss Hss.
by apply/(Ctxt.get_Some_in_dom _ _ ss).
Qed.

Module Ctyp.

Record t (g : wfctxt) : Type := mk {
  ty :> typ ;
  Hty : cover g ty }.

End Ctyp.

Coercion Ctyp_coercion := Ctyp.ty.

Canonical Ctyp_subType g := [subType for (@Ctyp.ty g)].
Definition Ctyp_eqMixin g := Eval hnf in [eqMixin of @Ctyp.t g by <:].
Canonical Ctyp_eqType g := Eval hnf in EqType (@Ctyp.t g) (@Ctyp_eqMixin g).

Notation "g '.-typ:' ty " := (Ctyp.mk g ty erefl) (at level 50) : C_types_scope.

Notation "g '.-typ'" := (Ctyp.t g) (at level 2, format "g '.-typ'") : C_types_scope.

Definition Cenv g := seq (string * g.-typ).

Notation "g '.-env'" := (Cenv g) (at level 2, format "g '.-env'") : C_types_scope.

Definition mkCenv (g : wfctxt) : forall (l : Fields.A) (H : forall x, x \in l -> cover g x.2),
  g.-env.
fix mkCenv 1.
intro l.
destruct l as [|h t].
intros _.
exact nil.
intro H.
apply cons.
apply pair.
exact h.1.
exists h.2.
move: (H h (mem_head _ _)) =>  /= H'.
destruct (cover g h.2).
apply refl_equal.
discriminate H'.
apply (mkCenv t).
intros x xt.
apply H.
apply (mem_tail _ xt).
Defined.

Lemma in_mkCenv {g : wfctxt}: forall (l : Fields.A) (H : forall x, x \in l -> cover g x.2) (x : string * g.-typ),
  x \in mkCenv g l H -> (x.1, Ctyp.ty _ x.2) \in l.
Proof.
elim => //= hd tl Hind H x.
rewrite inE.
destruct x.
case/orP.
- move/eqP => Heq.
  injection Heq => ? ?; subst.
  rewrite /= in_cons; apply/orP; left; destruct hd; done.
- move => Hindhyp.
  rewrite in_cons; apply/orP; right; apply (Hind _ _ Hindhyp).
Qed.

Definition get_fields' g tg : g.-env :=
  match option_dec (Ctxt.get tg g) with
    | inright H => nil
    | inleft l => mkCenv g (projT1 l) (wfctxt_get g tg (projT1 l) (projT2 l))
  end.

Definition get_fields := nosimpl get_fields'.

Lemma get_fields_in_dom : forall (g : wfctxt) str t tg,
  (str, t) \in get_fields g tg -> tg \in Ctxt.dom g.
Proof.
move=> g str t tg.
rewrite /get_fields /get_fields'.
destruct (option_dec (Ctxt.get tg g)) => // _.
case: s => s Hs.
by apply Ctxt.get_Some_in_dom with s.
Qed.

Module ctxt_prop_m := finmap.Map_Prop Ctxt.

Lemma wfctxt_get_fields_not_empty g (t : g.-typ) tg (H : Ctyp.ty _ t = styp tg) : get_fields g tg <> nil.
Proof.
move: (wfctxt_has_no_empty g) => Hno_empty.
rewrite /no_empty in Hno_empty.
rewrite /get_fields /get_fields'.
destruct g as [x w] => //=.
simpl in Hno_empty.
have Hget: Ctxt.get tg x <> None.
  suff: exists v, Ctxt.get tg x = Some v by move => [] v ->.
  apply Ctxt.in_dom_get_Some => //.
  destruct t as [x0 i] => //.
  destruct x0 as [| | | tg0] => //.
  rewrite /= in H.
  case: H => <-.
  rewrite /= /cover in i.
  move/incP' : i; apply.
  by rewrite /= in_cons eqxx.
move: (Ctxt.get_Some_in_cdom x tg) => Hcdom.
case: option_dec => //=; move=> [] v Hv /=.
move: {Hcdom Hno_empty}(Hno_empty _ (Hcdom _ Hv)) => Hno_empty.
by destruct v.
Qed.

Lemma size0_get_fields {g : wfctxt} tg : size (Ctxt.dom g) = 0 -> get_fields g tg = nil.
Proof.
destruct g as [g Hg] => /=.
move=> Hsz.
apply ctxt_prop_m.size0_emp in Hsz.
subst g.
rewrite /get_fields /get_fields'.
case: option_dec => //.
case=> l Hl /=.
exfalso.
by rewrite Ctxt.get_emp in Hl.
Qed.

Obligation Tactic := idtac.

Program Definition get_fields_mkCenv_statement := forall (g : wfctxt) tg
  x (Hx : Ctxt.get tg g = Some x) l (Hl : get_fields g tg = l),
  l = mkCenv g x _.
Next Obligation.
move => g tg x Hx l Hl hd Hhd.
apply (wfctxt_get _ _ _ Hx) => //.
Defined.

Obligation Tactic := Tactics.program_simpl.

Lemma get_fields_mkCenv : get_fields_mkCenv_statement.
Proof.
rewrite /get_fields_mkCenv_statement.
move=> g tg x Hx l Hl.
have Hx' : Ctxt.get tg g = Some x by done.
have -> : Hx = Hx' by apply eq_irrelevance.
have Hl' : get_fields g tg = l by done.
(*have -> : Hl = Hl' by apply/eq_irrelevance.*)
destruct g as [g Hg].
rewrite /get_fields /get_fields' in Hl.
simpl in Hl.
destruct (option_dec (Ctxt.get tg g)).
  simpl in Hx'.
  clear Hx.
  have ? : projT1 s = x.
    case: s Hl => s Hs _ /=.
    rewrite Hx' in Hs.
    by case: Hs.
  subst x.
  rewrite -{1}Hl /=.
  congr mkCenv.
  by apply ProofIrrelevance.proof_irrelevance.
exfalso.
by rewrite /= e in Hx.
Qed.

Notation "'ityp:' t " := (_.-typ: ityp t) (at level 50, format "'ityp:'  t") : C_types_scope.

Notation "g '.-ityp:' t " := (Ctyp.mk g (ityp t) Logic.eq_refl) (at level 50, format "g '.-ityp:'  t") : C_types_scope.

Definition mkptyp {g} (t : g.-typ) := Ctyp.mk g (ptyp (Ctyp.ty _ t)) (Ctyp.Hty _ t).

Notation "':*' t " := (mkptyp t) (at level 50, format "':*'  t") : C_types_scope.

Lemma Ctyp_ptyp_inj {g} : forall (t1 t2 : g.-typ), :* t1 = :* t2 -> t1 = t2.
Proof.
move=> [t1 p1] [t2 p2] /= [] t1t2; move: p1 p2; rewrite t1t2 => p1 p2.
congr Ctyp.mk.
by apply eq_irrelevance.
Qed.

Definition Ctyp_styp {g : wfctxt} : forall (s : {tg : tag | cover g (styp tg)}), g.-typ.
move => [] ty Hty.
by apply (Ctyp.mk g (styp ty)).
Defined.

Definition Ctyp_styp' {g : wfctxt} {tg : tag} (H : cover g (styp tg)) : g.-typ :=
  Ctyp.mk _ _ H.

Lemma Ctyp_styp'_sval {g : wfctxt} : forall {tg} {H : cover g (styp tg)},
  Ctyp.ty _ (Ctyp_styp' H) = styp tg.
Proof. by []. Qed.

Definition atyp_styp {g} : forall {ty : g.-typ} {sz} {Hz} {tg : tag} (H : Ctyp.ty _ ty = atyp sz Hz tg),
  {s: tag | cover g (styp s)}.
case => //= ty Hty sz Hsz s Htys.
destruct ty => //=.
case: Htys => H1 H2; subst.
by exists s.
Defined.

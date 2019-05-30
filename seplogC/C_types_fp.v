(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Coq.Program.Wf FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat.
From mathcomp Require Import div path tuple.
Require Import Init_ext String_ext Max_ext.
Require Import seq_ext ssrnat_ext tuple_ext path_ext.
Require order finmap.
Require Import C_types.

Local Close Scope Z_scope.

Section dmap_sect.

Variable A : eqType.
Variable B : Type.
Variable k : seq A.
Variable f : forall (x : A), x \in k -> B.

Obligation Tactic := idtac.

Program Fixpoint dmap (l : seq A) (Hl : {subset l <= k}) {struct l} : seq B :=
  match l with
    | nil => nil
    | h :: t => (f h (Hl h (mem_head h t))) :: dmap t _
  end.
Next Obligation.
intros l lk h t Hl.
rewrite -Hl.
reflexivity.
Qed.
Next Obligation.
intros l lk h t Hl x x_t.
apply lk.
rewrite -Hl.
apply mem_tail.
exact x_t.
Defined.

End dmap_sect.

Arguments dmap [A] [B] _ _ _ _.

Section dmapP_sect.

Variable A : eqType.
Variable B : Type.
Variable P : A -> bool.
Variable f : forall (x : A), P x -> B.

(* map with a function f whose domain is restricted by P
   (and thus only works for lists whose domain satisfies P) *)
Program Fixpoint dmapP (l : seq A) (Hl : forall x, x \in l -> P x) {struct l} : seq B :=
  match l with
    | nil => nil
    | h :: t => (f h (Hl h (mem_head h t))) :: dmapP t _
  end.
Next Obligation.
by apply (Hl x (mem_tail h H)).
Defined.

Variable f' : A -> B.
Hypothesis ff' : forall x (Px : P x), f x Px = f' x.

(* dmapP f is the same as map f' if f and f'' coincide on P *)
Lemma dmapP_map (l l': seq A) (Hl : forall x, x \in l -> P x) :
  l = l' -> dmapP l Hl = map f' l'.
Proof.
move <-.
elim: l Hl => //= hd tl Hind Hl.
by rewrite ff' Hind.
Qed.

End dmapP_sect.

Arguments dmapP [A] [B] _ _ _ _.
Arguments dmapP_map [A] [B] _ _ _ _ _ _ _ _.

Section dmap_dmapP.

Variable A : eqType.
Variable B : Type.
Variable k : seq A.
Variable f : forall (x : A), x \in k -> B.

Lemma dmap_dmapP : forall l H1,
  dmap k f l H1 = dmapP (fun x => x \in k) f l H1.
Proof.
elim => //= h t IH H1.
congr cons.
  congr (f h (H1 _ _)).
  by apply eq_irrelevance.
by rewrite IH.
Qed.

End dmap_dmapP.

Section dmapP_prop_sect.

Variable A : eqType.
Variables B C : Type.
Variable PA : A -> bool.
Variable f : forall (x : A), PA x -> B.
Variable PA' : A -> bool.
Variable f' : forall (x : A), PA' x -> B.
Hypothesis ff' : forall x PAx PA'x, f x PAx = f' x PA'x.

Lemma dmapP_ext (l l': seq A) : l = l' ->
  forall (Hl: forall x, x \in l -> PA x) (Hl' : forall x, x \in l' -> PA' x) ,
  dmapP PA f l Hl = dmapP PA' f' l' Hl'.
Proof.
move <-.
elim: l => //= h t Hind Hl Hl'.
congr cons.
by apply ff'.
by apply Hind.
Qed.

Variable PB : B -> Prop.
Variable PC : C -> Prop.
Variable PC' : C -> Prop.
Hypothesis PC_PC' : forall x, PC x -> PC' x.

Lemma foldl_dmapP_pred
  (PBf : forall x PAx, PB (f x PAx))
  (f_foldl : C -> B -> C)
  (Hffoldl : forall b (Hb: PB b) c (Hc: PC' c), PC (f_foldl c b)) :
  forall
    (l: seq A) (Hl0 : l <> nil) (Hl : forall x, x \in l -> PA x)
    (acc : C) (PC'acc : PC' acc),
    PC (foldl f_foldl acc (dmapP PA f l Hl)).
Proof.
elim => //= hd tl.
case: (tl =P nil).
- move => -> Hind Hl1 Hl2 acc Hacc => /=.
  by apply Hffoldl.
- move => Hneq Hind Hl1 Hl2 acc Hacc.
  by apply (Hind Hneq), PC_PC', Hffoldl.
Qed.

End dmapP_prop_sect.

Arguments dmapP_ext [A] [B] _ _ _ _ _ _ _ _ _ _.
Arguments foldl_dmapP_pred [A B C] _ _ _ _ _ _ _ _ _ _ _ _ _ _.

Section Fix_spec.

Variables Arg Res : Type.
Variable metric : Arg -> nat.
Hypothesis well_founded_metric : well_founded (fun a a' => metric a < metric a').

Variable frec0 : forall a : Arg, (forall a', metric a' < metric a -> Res) -> Res.

Definition frec := Fix well_founded_metric (fun _ => Res) frec0.

Lemma frec_unfold a : frec a = frec0 a (fun a' _ => frec a').
Proof.
rewrite /frec Init.Wf.Fix_eq; first by reflexivity.
move=> a' f g fg.
congr frec0.
apply functional_extensionality_dep => a0.
by apply functional_extensionality.
Qed.

Program Fixpoint frec_ind (P : Res -> Prop)
  (IH : forall a f', (forall a0 a0a, P (f' a0 a0a)) -> P (frec0 a f'))
  a {measure (metric a)} : P (frec a) := _.
Next Obligation.
rewrite frec_unfold.
apply IH => a0 /ltP; move: a0.
by apply frec_ind.
Qed.

Variable C : Type.

Variable input : Arg -> C.

Lemma A1 : forall (a : Arg)
  (f : forall a' : Arg, metric a' < metric a -> Res),
  (forall (a1 : Arg) (H1 : metric a1 < metric a)
          (a2 : Arg) (H2 : metric a2 < metric a),
   input a1 = input a2 -> metric a2 < metric a1 -> f a1 H1 = f a2 H2) ->
  forall a' : Arg,
    metric a' < metric a ->
    input a = input a' ->
  forall x : Arg,
  metric x < metric a' -> (metric x < metric a') = (metric x < metric a).
Proof.
move => a f Hind a' Hmetric Hinput x Hx.
by rewrite Hx (ltn_trans Hx Hmetric).
Qed.

Lemma A2 : (forall (a : Arg) (f : forall a' : Arg, metric a' < metric a -> Res)
   (H : forall (a1 : Arg) (H1 : metric a1 < metric a)
               (a2 : Arg) (H2 : metric a2 < metric a),
    input a1 = input a2 -> metric a2 < metric a1 -> f a1 H1 = f a2 H2)
   (a' : Arg) (H0 : metric a' < metric a) (H1 : input a = input a'),
 frec0 a f =
 frec0 a'
   (fun (x : Arg) (x0 : metric x < metric a') =>
    f x
      (eq_rect (metric x < metric a') (eq^~ true) x0
         (metric x < metric a)
         (A1 a f H a' H0 H1 x x0)))) ->
forall a a' : Arg,
input a = input a' ->
metric a' < metric a ->
((forall (a0 : Arg) (f' : forall a'0 : Arg, metric a'0 < metric a0 -> Res)
    (H : forall (a1 : Arg) (H1 : metric a1 < metric a0)
           (a2 : Arg) (H2 : metric a2 < metric a0),
         input a1 = input a2 -> metric a2 < metric a1 -> f' a1 H1 = f' a2 H2)
    (a'0 : Arg) (H0 : metric a'0 < metric a0) (H1 : input a0 = input a'0),
  frec0 a0 f' =
  frec0 a'0
    (fun (x : Arg) (x0 : metric x < metric a'0) =>
     f' x
       (eq_rect (metric x < metric a'0) (eq^~ true) x0
          (metric x < metric a0)
          (A1 a0 f' H a'0 H0 H1 x x0)))) ->
 forall a0 a'0 : Arg,
 input a0 = input a'0 ->
 metric a'0 < metric a0 ->
 (metric a0 < metric a)%coq_nat -> frec a0 = frec a'0) ->
frec a = frec a'.
Proof.
move => Hind a a' Hinput Hmetric Hfix.
rewrite frec_unfold.
have H : (forall a1 : Arg,
     metric a1 < metric a ->
     forall a2 : Arg,
     metric a2 < metric a -> input a1 = input a2 -> metric a2 < metric a1 -> frec a1 = frec a2).
  move => a1 Ha1 a2 Ha2 Ha12 Hl12.
  apply Hfix => //.
  by apply/ltP.
move: {H}(Hind a ((fun (a'0 : Arg) (_ : metric a'0 < metric a) => frec a'0)) H a' Hmetric Hinput) => ->.
symmetry.
apply frec_unfold.
Qed.

Program Fixpoint frec_ext
(Hind :
    forall a
      (f: forall (a': Arg) (H: metric a' < metric a), Res)
      (K : forall a1 H1 a2 H2, input a1 = input a2 -> metric a2 < metric a1 -> f a1 H1 = f a2 H2),
      forall a' (H: metric a' < metric a) (H1 : input a = input a'), frec0 a f = frec0 a'
(fun (x : Arg) (x0 : metric x < metric a') =>
 f x
   (eq_rect (metric x < metric a') (eq^~ true) x0
      (metric x < metric a)
      (A1 a f K a' H H1 x x0)))
)
  a a' (Heq: input a = input a') (Hlt: metric a' < metric a) {measure (metric a)} :
  frec a = frec a' := A2 Hind a a' Heq Hlt frec_ext.

End Fix_spec.

Local Open Scope C_types_scope.

Section generic_traversal.

Variable g : wfctxt.

Record config {Res Accu : Type} := mkConfig {
  f_ityp : integral -> Res ;
  f_ptyp : typ -> Res ;
  f_styp_iter : Accu -> string * g.-typ * Res -> Accu ;
  f_styp_fin : tag * g.-typ -> (Accu -> Accu) -> Res ;
  f_atyp : nat -> tag * g.-typ -> Res -> Res }.

Record Trace : Type := mkTrace {
  trace_size : nat ;
  trace :> PathNested.t g trace_size }.

Definition next_path_styp {n} (p : PathNested.t g n)
  tg (Htg : cover g (styp tg))
  str (Hin : (str, Ctyp.mk g (styp tg) Htg) \in get_fields g (tlast p)) :
  {p_tg : PathNested.t g n.+1 | tlast p_tg = tg}.
set p_tg := trcons p tg.
have Hp1 : (thead p_tg \in Ctxt.dom g) /\ path (nested g) (thead p_tg) (behead p_tg).
  split.
  - rewrite /p_tg thead_trcons; exact (PathNested.Hp1 _ _ p).
  - rewrite /p_tg thead_trcons behead_trcons rcons_path; apply/andP; split.
    + clear -p; exact (PathNested.Hp _ _ p).
    + rewrite /nested.
      have : tlast p \in Ctxt.dom g by move: Hin; apply get_fields_in_dom.
      case/Ctxt.in_dom_get_Some => flds Hflds.
      rewrite Hflds.
      apply/hasP.
      exists (str, styp tg).
      * rewrite (get_fields_mkCenv g _ flds Hflds (get_fields g (tlast p)) Logic.eq_refl) in Hin.
        by apply (in_mkCenv _ _ _ Hin).
      * by rewrite /= eqxx.
exists (PathNested.mkt _ _ _ (proj1 Hp1) (proj2 Hp1)).
by rewrite /= /p_tg tlast_trcons.
Defined.

Definition next_path_atyp {n} (p : PathNested.t g n)
  (tg : tag) sz Hsz (Hs : cover g (atyp sz Hsz tg))
  str (Hin : (str, Ctyp.mk g (atyp sz Hsz tg) Hs) \in get_fields g (tlast p)) :
  {p0 : PathNested.t g n.+1 | tlast p0 = tg}.
set p1 := trcons p tg.
have Hp1 : (thead p1 \in Ctxt.dom g) /\ path (nested g) (thead p1) (behead p1).
  split.
  - by rewrite -thead_tbelast /p1 thead_tbelast thead_trcons; exact (PathNested.Hp1 _ _ p).
  - rewrite /p1 thead_trcons behead_trcons rcons_path; apply/andP; split.
    + exact (PathNested.Hp _ _ p).
    + rewrite /nested.
      case: (Ctxt.in_dom_get_Some g (tlast (A:=tag_eqType) p)).
      * by move: Hin; apply get_fields_in_dom.
      * move => x Hx.
        rewrite Hx.
        apply/hasP.
        exists (str, atyp sz Hsz tg).
        - move: Hin.
          rewrite (get_fields_mkCenv _ _ _ Hx (get_fields g (tlast p)) Logic.eq_refl).
          by apply in_mkCenv.
        - by simpl.
exists (PathNested.mkt _ _ _ (proj1 Hp1) (proj2 Hp1)) => //=;
by rewrite /p1 //= /p1 tlast_trcons.
Defined.

Variables Res Accu : Type.
Variable c : @config Res Accu.

Definition remains t := size (Ctxt.dom g) - trace_size t.

Lemma well_founded_remains : well_founded (fun a a' : Trace => remains a < remains a').
Proof.
apply Wf_nat.well_founded_lt_compat with remains => x y xy.
by apply/leP.
Defined.

Obligation Tactic := idtac.

Program Definition styp_frec0 (t : Trace)
  (f : forall t', remains t' < remains t -> Res) : Res :=
  match t with
    | mkTrace n p =>
      let tg := tlast p in
      let env := get_fields g tg in
      let l := dmap env
            (fun x Hx => (x,
              match Ctyp.ty _ x.2 with
                | ityp i => c.(f_ityp) i
                | ptyp p => c.(f_ptyp) p
                | styp tg' => f (mkTrace n.+1 _) _
                | atyp sz Hsz tg' =>
                  c.(f_atyp) sz (tg', Ctyp.mk g (styp tg') _) (f (mkTrace n.+1 _) _)
              end)) env (id (fun x (Hx : x \in env) => Hx)) in
          c.(f_styp_fin) (tg, Ctyp.mk g (styp tg) _) (fun accu => foldl c.(f_styp_iter) accu l)
  end.
Next Obligation.
move=> tr Htr n p p_tr tg env str_cov str_cov_in_env sval_str_cov2 tg' Heq1 /=.
rewrite /env {env} in str_cov_in_env.
rewrite /sval_str_cov2 {sval_str_cov2} in Heq1.
destruct str_cov as [str [t cov_t]].
rewrite /= in Heq1 *.
rewrite /tg in str_cov_in_env.
subst t.
apply (next_path_styp p tg' cov_t str str_cov_in_env).
Defined.
Next Obligation.
move=> tr Htr n p p_tr tg env str_cov str_cov_in_env sval_str_cov2 tg' Heq1 /=.
rewrite /env in str_cov_in_env *.
rewrite /sval_str_cov2 in Heq1 *.
destruct str_cov as [str [t cov_t]].
simpl in *.
subst t.
destruct p as [p Hp].
simpl in *.
destruct tr as [tr1 tr2].
rewrite /remains /= ltn_sub2l //.
by apply uniq_path_size_complete_ub.
case: p_tr => Hn _; by rewrite Hn.
Defined.
Next Obligation.
move=> t Ht n p pt tg env str_cov str_cov_in_env sval_str_cov2 sz Hsz tg' He1 /=.
rewrite /sval_str_cov2 in He1.
destruct str_cov as [str [ty cov_ty]].
simpl in *.
clear str_cov_in_env.
by rewrite -He1 in cov_ty.
Defined.
Next Obligation.
move=> tr Htr n p p_tr tg env str_cov str_cov_in_env sval_str_cov2 sz Hsz tg' Heq1 /=.
rewrite /env in str_cov_in_env.
rewrite /sval_str_cov2 in Heq1.
destruct str_cov as [str [t cov_t]].
simpl in *.
subst t.
rewrite /tg in str_cov_in_env.
apply (next_path_atyp p tg' sz Hsz cov_t str str_cov_in_env).
Defined.
Next Obligation.
move=> tr Htr n p p_tr tg env str_cov str_cov_in_env sval_str_cov2 sz Hsz tg' Heq1 /=.
rewrite /env in str_cov_in_env *.
rewrite /sval_str_cov2 in Heq1 *.
destruct str_cov as [str [t cov_t]].
simpl in *.
subst t.
simpl in *.
destruct tr as [tr1 tr2].
rewrite /remains /= ltn_sub2l //.
by apply uniq_path_size_complete_ub.
case: p_tr => Hn _; by rewrite Hn.
Defined.
Next Obligation.
move=> tr f n p p_tr tg env l.
clear l.
have : tg \in PathNested.p _ _ p.
  destruct p as [p H1 H2] => /=.
  by rewrite /tg /tlast (last_nth (thead p)) [in X in _ \in X](tuple_eta p) mem_nth.
move/in_path_in_dom => tg_p.
by apply in_dom_cover.
Defined.

Definition styp_frec := Fix well_founded_remains (fun _ => Res) styp_frec0.

Program Definition typ_traversal (ty : g.-typ) : Res :=
  match Ctyp.ty _ ty with
    | ityp i => c.(f_ityp) i
    | ptyp p => c.(f_ptyp) p
    | styp tg => styp_frec (mkTrace 0 _)
    | atyp sz _ tg => c.(f_atyp) sz (tg, Ctyp.mk g (styp tg) _) (styp_frec (mkTrace  0 _))
end.
Next Obligation.
move=> ty fil_ty tg tg_ty /=.
set p := [tuple tg].
have Hp : (thead p \in Ctxt.dom g) /\ path (nested g) (thead p) (behead p).
  split.
  - rewrite /p theadE.
    move/incP': (Ctyp.Hty _ ty); apply.
    by rewrite -/fil_ty -tg_ty /= mem_seq1.
  - reflexivity.
exists (PathNested.mkt _ _ _ (proj1 Hp) (proj2 Hp)) => //=; exact (proj1 Hp). 
Defined.
Next Obligation.
case=> //= t cov_t sz Hsz tg tg_t.
by subst t.
Defined.
Next Obligation.
move=> ty fil_ty sz Hsz tg tg_ty /=.
set p := [tuple tg].
have Hp : (thead p \in Ctxt.dom g) /\ path (nested g) (thead p) (behead p).
  split.
  - rewrite /p theadE.
    move/incP': (Ctyp.Hty _ ty); apply.
    by rewrite -/fil_ty -tg_ty /= mem_seq1.
  - reflexivity.
exists (PathNested.mkt _ _ _ (proj1 Hp) (proj2 Hp)) => //=; exact (proj1 Hp).
Defined.

Program Definition typ_traversal_unfold_statement := forall ty, typ_traversal ty =
  match Ctyp.ty _ ty with
    | ityp i => c.(f_ityp) i
    | ptyp p => c.(f_ptyp) p
    | styp tg => c.(f_styp_fin) (tg, Ctyp.mk g (styp tg) _)
                  (fun accu => foldl c.(f_styp_iter) accu
                    (map (fun x => (x, typ_traversal x.2)) (get_fields g tg)))
    | atyp sz Hsz tg => c.(f_atyp) sz (tg, Ctyp.mk g (styp tg) _) (c.(f_styp_fin) (tg, Ctyp.mk g (styp tg) _)
                         (fun accu => foldl c.(f_styp_iter) accu
                           (map (fun x => (x, typ_traversal x.2)) (get_fields g tg))))
  end.
Next Obligation.
move=> ty fil_ty tg ->; apply (Ctyp.Hty _ ty).
Defined.
Next Obligation.
case=> //= t cov_t sz Hsz tg Htg; by rewrite -Htg in cov_t.
Defined.
Next Obligation.
case=> //= t cov_t sz Hsz tg Htg; by rewrite -Htg in cov_t.
Defined.

Obligation Tactic := Tactics.program_simpl.

Lemma styp_frec0_ext (a : Trace)
     (f : forall a' : Trace, remains a' < remains a -> Res)
     (H : forall (a1 : Trace) (H1 : remains a1 < remains a)
            (a2 : Trace) (H2 : remains a2 < remains a),
          tlast a1 = tlast a2 ->
          remains a2 < remains a1 -> f a1 H1 = f a2 H2)
     (a' : Trace) (H0 : remains a' < remains a)
     (H1 : tlast a = tlast a') :
   styp_frec0 a f =
   styp_frec0 a'
     (fun (x : Trace) (x0 : remains x < remains a') =>
      f x
        (eq_rect (remains x < remains a') (eq^~ true) x0
           (remains x < remains a)
           (A1 Trace Res remains _ (fun x => tlast x) a f H a' H0 H1 x x0))).
Proof.
destruct a as [n p].
destruct a' as [n' p'].
rewrite /= in H1 *.
move: (styp_frec0_obligation_6 _ _ _ _) => H1'.
move: (styp_frec0_obligation_6 _ _ _ _) => H2'.
congr (f_styp_fin c (_ , _)) => //.
  move: H1' H2' => /= H1'.
  rewrite -H1 => H2'.
  congr Ctyp.mk.
  by apply eq_irrelevance.
apply functional_extensionality => accu.
congr foldl.
rewrite !dmap_dmapP.
apply dmapP_ext; last by rewrite H1.
move => x Hx Hx'.
congr pair.
case: x Hx Hx' => x [t Ht] Hx Hx'.
rewrite /fst /snd.
case: t Ht Hx Hx' => [i | t | tg' | sz Hsz tg'] x3 Hx Hx'.
- reflexivity.
- reflexivity.
- apply H => //=.
    clear -H1.
    by rewrite 2!tlast_trcons.
  rewrite /remains !subnS prednK; last first.
    rewrite subn_gt0.
    apply uniq_path_size_complete_ub.
    exact p'.
  by rewrite -ltnS prednK // (leq_ltn_trans _ H0).
- rewrite /=.
  congr (f_atyp _ _ _ _).
  apply H => //=.
    clear -H1.
    by rewrite 2!tlast_trcons.
  rewrite /remains !subnS prednK; last first.
    rewrite subn_gt0.
    apply uniq_path_size_complete_ub.
    exact p'.
  by rewrite -ltnS prednK // (leq_ltn_trans _ H0).
Qed.

Lemma pair_eq : forall (A B : Type) (x1 x2: A) (y1 y2: B),
  x1 = x2 -> y1 = y2 -> (x1, y1) = (x2, y2).
Proof. by move => ? ? ? ? ? ? -> ->. Qed.

Lemma typ_traversal_unfold : typ_traversal_unfold_statement.
Proof.
rewrite /typ_traversal_unfold_statement.
case.
rewrite /typ_traversal /=.
case => //= [t p | sz i t p].
- rewrite /styp_frec.
  rewrite -/(frec Trace Res remains well_founded_remains styp_frec0).
  rewrite {1}frec_unfold /=.
  congr (f_styp_fin c _ _).
    congr (_, Ctyp.mk _ _ _).
    by apply eq_irrelevance.
  apply functional_extensionality => accu.
  congr foldl.
  set l1 := get_fields _ _.
  rewrite !dmap_dmapP.
  apply dmapP_map with (l := l1).
  * move => [x1 [x2 x3]] Hx.
      rewrite /fst /snd.
      apply pair_eq; first by reflexivity.
      case: x2 x3 Hx => //= [tg x3 Hx| sz Hsz tg x3 Hx].
      - symmetry.
        apply (frec_ext _ Res remains _ styp_frec0 _ (fun x => tlast x)) => //.
        + by apply styp_frec0_ext.
        + rewrite /remains /= subn0 subn1 -ltnS (@ltn_predK 0) // -has_predT.
          apply/hasP. exists tg => //.
          by move: x3 {Hx}; rewrite /cover; move/incP'; apply; rewrite mem_head.
      - congr f_atyp.
        apply/esym/(frec_ext _ Res remains _ styp_frec0 _ (fun x => tlast x)) => //.
        + by apply styp_frec0_ext.
        + rewrite /remains /= subn0 subn1 -ltnS (@ltn_predK 0) // -has_predT.
          apply/hasP. exists tg => //.
          by move: x3 {Hx}; rewrite /cover; move/incP'; apply; rewrite mem_head.
  * reflexivity.
- congr f_atyp.
  rewrite /styp_frec.
  rewrite -/(frec Trace Res remains well_founded_remains styp_frec0).
  rewrite {1}frec_unfold /=.
  congr f_styp_fin.
    congr (_, Ctyp.mk _ _ _).
    by apply eq_irrelevance.
  apply functional_extensionality => accu.
  congr foldl.
  set l1 := get_fields _ _.
  rewrite !dmap_dmapP.
  apply dmapP_map with (l := l1).
  * move => [x1 [x2 x3]] Hx.
    rewrite /fst /snd.
    apply pair_eq; first by done.
    case: x2 x3 Hx => //= [tg x3 Hx| sz' Hsz' tg x3 Hx].
    - apply/esym/(frec_ext _ Res remains _ styp_frec0 _ (fun x => tlast x)) => //.
      + by apply styp_frec0_ext.
      + rewrite /remains /= subn0 subn1 -ltnS (@ltn_predK 0) // -has_predT.
        apply/hasP. exists tg => //.
        by move: x3 {Hx}; rewrite /cover; move/incP'; apply; rewrite mem_head.
    - congr f_atyp.
      apply/esym/(frec_ext _ Res remains _ styp_frec0 _ (fun x => tlast x)) => //.
      + by apply styp_frec0_ext.
      + rewrite /remains /= subn0 subn1 -ltnS (@ltn_predK 0) // -has_predT.
        apply/hasP. exists tg => //.
        by move: x3 {Hx}; rewrite /cover; move/incP'; apply; rewrite mem_head.
  * reflexivity.
Qed.

Variable PRes : Res -> Prop.
Variable PAcc1 : Accu -> Prop.
Variable PAcc2 : Accu -> Prop.
Hypothesis PAcc12 : forall a : Accu, PAcc1 a -> PAcc2 a.
Hypothesis Hityp : forall (i : integral), PRes (c.(f_ityp) i).
Hypothesis Hptyp : forall (t : typ), PRes (c.(f_ptyp) t).
Hypothesis Hiter :
  forall ty (r : Res) (Ha : PRes r) b (Hb : PAcc2 b), PAcc1 (c.(f_styp_iter) b (ty, r)).
Hypothesis Hfin : forall a_trans tg_ty,
  (forall a : Accu, PAcc2 a -> PAcc1 (a_trans a)) -> PRes (c.(f_styp_fin) tg_ty a_trans).
Hypothesis Hatyp :
  forall sz (Hsz : sz > 0) ty a (Ha : PRes a), PRes (c.(f_atyp) sz ty a).

Lemma styp_frec_ind n p : PRes (styp_frec (mkTrace n p)).
Proof.
rewrite /styp_frec.
fold (frec Trace Res remains well_founded_remains styp_frec0).
apply frec_ind => a f' H.
destruct a as [a1 a2] => /=.
apply Hfin.
rewrite !dmap_dmapP.
apply (foldl_dmapP_pred _ _ (fun x => PRes x.2) _ _ PAcc12) => //=.
+ move => [name [t Ht]] Hx.
  case: t Ht Hx => //= sz Hsz t Ht Hx.
  by apply Hatyp.
+ case => *.
  by apply Hiter.
+ have i : cover g (styp (last (thead a2) (behead a2))).
    apply in_dom_cover.
    apply in_path_in_dom with a1 a2.
    destruct a2 => /=.
    rewrite (last_nth (thead p0)).
    rewrite size_tuple /=.
    rewrite [in X in _ \in X](tuple_eta p0).
    apply mem_nth => /=.
    by rewrite size_behead size_tuple.
  by apply wfctxt_get_fields_not_empty with (Ctyp.mk g _ i).
Qed.

Lemma typ_traversal_ind : forall t, PRes (typ_traversal t).
Proof.
move => [] []; rewrite /typ_traversal //=.
- move => tg p.
  by apply styp_frec_ind.
- move => sz Hsz tg p.
  apply Hatyp => //.
  by apply styp_frec_ind.
Qed.

End generic_traversal.

Arguments mkConfig _ [Res Accu].
Arguments typ_traversal _ [Res Accu].
Arguments typ_traversal_ind _ [Res Accu].

(** alignment *)

(* here in hard for computation *)
Definition align_ptr := 4.

Definition align_integral t :=
  match t with uint => 4 | sint => 4 |
  uchar => 1 | schar => 1 | ulong => 8 end.

Definition align_config g := mkConfig g
  align_integral
  (fun _ => align_ptr)
  (fun a x => maxn x.2 a) (fun _ x => x 1)
  (fun _ _ x => x).

Definition align {g} := typ_traversal g (align_config g).

Lemma align_ind (P : nat -> Prop)
  (Hityp : forall t, P (align_integral t))
  (Hptyp : P (align_ptr))
  (Hacc : P 1)
  (Hiter : forall a (Ha : P a) b (Hb : P b), P (maxn a b)) :
  forall {g} (ty : g.-typ), P (align ty).
Proof.
move => g ty.
rewrite /align.
by apply typ_traversal_ind with P P => //= b _; apply.
Qed.

Lemma align_gt0 {g} (t : g.-typ) : 0 < align t.
Proof.
apply align_ind => //.
- by case.
- move => a Ha b Hb.
  rewrite /maxn; by case: ifP.
Qed.

Lemma align_discrete_values {g} (t : g.-typ) :
  align t \in 1 :: 4 :: 8 :: align_ptr :: nil.
Proof.
apply align_ind => //=.
- by case.
- move => a Ha; apply/allP.
  move: a Ha; by apply/allP.
Qed.

Lemma align_styp {g} : forall (t : g.-typ) tg (H : Ctyp.ty _ t = styp tg),
  align t = foldl maxn 1 (map (fun x => align x.2) (get_fields g tg)).
Proof.
rewrite /align => ty tg H.
rewrite typ_traversal_unfold => //=.
destruct ty => //=.
destruct ty => //=.
simpl in H.
injection H => Heq; subst tg.
rewrite !foldl_map //=.
set l1 := get_fields _ _.
apply foldl_congr_f => n p.
apply maxnC.
Qed.

Lemma align_styp_min {g} (t : g.-typ) tg (H : Ctyp.ty _ t = styp tg) t' :
  t' \in unzip2 (get_fields g tg) -> align t' <= align t.
Proof.
move/mapP => [] x Hx ->.
rewrite (align_styp t tg H).
apply in_foldl_maxn.
by apply/mapP; exists x.
Qed.

Lemma align_styp_div {g} (t : g.-typ) tg (H : Ctyp.ty _ t = styp tg) t' :
  t' \in unzip2 (get_fields g tg) -> align t' %| align t.
Proof.
move => //= Hin.
move: (align_styp_min _ _ H _ Hin) => {Hin}.
apply/implyP.
move: (align t') (align_discrete_values t').
apply/allP.
move: (align t) (align_discrete_values t).
by apply/allP.
Qed.

Lemma align_atyp_styp {g} sz i tg H1 H2:
  align (Ctyp.mk g (atyp sz i tg) H1) = align (Ctyp.mk g (styp tg) H2).
Proof.
rewrite /align /typ_traversal /=.
congr (styp_frec _ _ _ _ (mkTrace _ _ _)).
suff -> : H2 = H1 by done.
by apply eq_irrelevance.
Qed.

Lemma align_get_fields : forall g (ty : g.-typ) tg (H : Ctyp.ty _ ty = styp tg) str_dummy ty_dummy,
  (str_dummy, ty_dummy) \in get_fields g tg ->
  forall i, (i < size (get_fields g tg))%nat ->
    align (nth (str_dummy, ty_dummy) (get_fields g tg) i).2 %| align ty.
Proof.
move => g ty tg H str_dummy ty_dummy Hin i Hi.
apply (align_styp_div _ _ H _).
set x := (nth _ _ _).
apply/mapP; exists x => //=.
by apply mem_nth.
Qed.

(** sizeof *)

Definition sizeof_ptr : nat := 4.
Definition ptr_len := sizeof_ptr * 8.

Definition sizeof_integral t :=
  match t with uint => 4 | sint => 4
  | uchar => 1 | schar => 1 | ulong => 8 end.

Definition sizeof_config g := mkConfig g
  sizeof_integral
  (fun _ => sizeof_ptr)
  (fun a x => a + padd a (align x.1.2) + x.2)
  (fun ty a => a 0 + padd (a 0) (align ty.2))
  (fun s _ r => muln s r).

Definition sizeof {g} := typ_traversal g (sizeof_config g).

Section sizeof_properties.

Variable g : wfctxt.

Lemma sizeof_ityp : forall t, sizeof (g.-ityp: t) = sizeof_integral t.
Proof. by case. Qed.

Lemma sizeof_ptyp : forall t : g.-typ, sizeof (:* t) = sizeof_ptr.
Proof. by case. Qed.

Lemma sizeof_foldl t tg (H : Ctyp.ty _ t = styp tg) :
  let c := sizeof_config g in
  sizeof t = (f_styp_fin g c) (tg, t)
    (fun acc => foldl (f_styp_iter g c) acc
       (map (fun x => (x, sizeof x.2)) (get_fields g tg))).
Proof.
move=> c.
rewrite /sizeof typ_traversal_unfold /=.
destruct t as [t Ht] => //=.
destruct t => //=.
move: H => /= H; case: H (H) => H; subst => _.
reflexivity.
Qed.

Lemma sizeof_ind (P : nat -> Prop) (PAcc : nat -> Prop)
  (HP : forall x, P x -> PAcc x)
  (Hityp : forall i, P (sizeof_integral i))
  (Hptyp : P sizeof_ptr)
  (Hacc : PAcc 0)
  (Hiter : forall (ty : string * g.-typ) n (Pn : P n) b (Hb : PAcc b),
    P (b + padd b (align ty.2) + n))
  (Hfin : forall (n : nat) (Pn : P n) (ty : tag * g.-typ), P (n + padd n (align ty.2)))
  (Hatyp : forall sz (Hsz : sz > 0) (n : nat) (Pn : P n), P (sz * n))
  (ty : g.-typ) : P (sizeof ty).
Proof.
rewrite /sizeof.
apply (typ_traversal_ind g (sizeof_config g) P P PAcc) => //.
- move => b ty' H; by apply Hfin, H.
- move => sz H /= _ a H0; by apply Hatyp.
Qed.

Lemma sizeof_gt0 : forall t : g.-typ, 0 < sizeof t.
Proof.
apply (sizeof_ind (fun x => 0 < x) (fun x => 0 <= x) )=> //=.
- by case.
- move => ty a Ha b Hb; by rewrite addnC ltn_addr.
- move => b Hb ty; by rewrite ltn_addr.
- move => sz Hsz a Ha; rewrite muln_gt0; by apply/andP.
Qed.

Lemma align_sizeof (t : g.-typ) : align t %| sizeof t.
Proof.
rewrite /sizeof typ_traversal_unfold //=.
destruct t as [t Ht]; destruct t => //.
- rewrite /=.
  set tmp := typ_traversal_unfold_statement_obligation_1 _ _ _ _.
  have -> : tmp = Ht by apply eq_irrelevance.
  by apply padd_isdiv, align_gt0.
- apply dvdn_mull.
  set tmp := foldl _ _ _.
  set a1 := align _.
  set a2 := align _.
  suff -> : a1 = a2 by apply padd_isdiv, align_gt0.
  by apply align_atyp_styp.
Qed.

End sizeof_properties.

Arguments align_sizeof [g] _.

Section foldl_sizeof.

Variables g : wfctxt.
Let f := fun a (h : string * g.-typ) => a + padd a (align h.2) + sizeof h.2.

Lemma ltn_foldl_foldl_aux : forall l i, i < size l -> forall a,
  foldl f a (take i l) +
    padd (foldl f a (take i l)) (align (nth (""%string, g.-ityp: uint) l i).2) <
      foldl f a l.
Proof.
elim=> // h t IH [_ a| i] /=.
- apply leq_trans with (a + padd a (align h.2) + sizeof h.2).
    rewrite -[X in X < _]addn0 ltn_add2l //.
    by apply sizeof_gt0.
  apply foldl_leq_monotonic => x str_t.
  by rewrite /f -addnA leq_addr.
- rewrite ltnS => it a.
  by apply IH.
Qed.

Lemma ltn_foldl_foldl : forall l i, i < size l -> forall b, b \in l ->
  forall a (t' : g.-typ),
  foldl f a (take (seq.index b l) l) +
    padd (foldl f a (take (seq.index b l) l)) (align (nth b l (seq.index b l)).2) <
      foldl f a l + padd (foldl f a l) (align t').
Proof.
case=> // hd tl i Hi def Hdef a ty.
apply ltn_leq_trans with (foldl f a (hd :: tl)).
- have -> : nth def (hd :: tl) (seq.index def (hd :: tl)) =
            nth (""%string, g.-ityp: uint) (hd :: tl) (seq.index def (hd :: tl)).
    apply set_nth_default.
    by rewrite index_mem.
  set j := seq.index def (hd :: tl).
  apply ltn_foldl_foldl_aux.
  by rewrite index_mem.
- by rewrite leq_addr.
Qed.

Lemma foldl_padd_size_aligned : forall (l : g.-env) a,
  (forall x, x \in l -> align x.2 %| a) ->
  forall a', foldl f (a + a') l = a + foldl f a' l.
Proof.
elim => //=.
move => hd tl Hind a Halign a'.
have Halign_hd: align hd.2 %| a by apply Halign; rewrite in_cons; apply/orP; left.
have Halign_tl: forall x, x \in tl -> align x.2 %| a by move => x Hx; apply Halign; rewrite in_cons; apply/orP; right.
case: (tl =P nil) => //= [Heq | Hneq].
- subst tl => //=.
  rewrite /f padd_add =>//; by nat_norm.
- rewrite -Hind => //=.
  rewrite /f padd_add =>//; by nat_norm.
Qed.

Lemma sizeof_leq_foldl : forall l (t' : g.-typ) str (t : g.-typ), (str, t) \in l ->
  forall a, a + sizeof t <= foldl f a l + padd (foldl f a l) (align t').
Proof.
elim => // hd tl IH t' str t Hin a.
move: Hin; rewrite in_cons; case/orP => [/eqP Hin | Hin].
  subst hd.
  rewrite /=.
  apply leq_trans with (a + padd a (align t) + sizeof t).
    by rewrite -addnA (addnC (padd _ _)) addnA leq_addr.
  apply leq_trans with (foldl f (a + padd a (align t) + sizeof t) tl).
    apply foldl_leq_monotonic => acc str_t.
    by rewrite /f -addnA leq_addr.
  by rewrite leq_addr.
rewrite /=.
apply leq_trans with (f a hd + sizeof t).
  by rewrite leq_add2r /f -addnA leq_addr.
by apply IH with str.
Qed.

Lemma leq_foldl_foldl : forall l i, i < size l ->
  forall str (t : g.-typ) , (str, t) \in l ->
  forall a tg (t' : g.-typ) (_ : Ctyp.ty _ t' = styp tg),
  foldl f a (take (seq.index (str, t) l) l) +
    padd (foldl f a (take (seq.index (str, t) l) l))
         (align (nth (str, t) l (seq.index (str, t) l)).2) +
      sizeof t <= foldl f a l.
Proof.
elim=> // h t IH [_ str ty Hin a tg t' tg_t' |i ].
- move: Hin; rewrite in_cons; case/orP => [/eqP | /= ] Hin.
    subst h.
    rewrite /= eqxx /=.
    apply foldl_leq_monotonic => acc str_t.
    by rewrite /f -addnA leq_addr.
  case: ifP => [/eqP ? | hb] /=.
    subst h.
    rewrite /=.
    apply foldl_leq_monotonic => acc str_t.
    by rewrite /f -addnA leq_addr.
  apply IH with O tg t' => //.
  by destruct t.
- rewrite /= ltnS => Hi str ty Hin a tg t' H.
  move: Hin; rewrite in_cons; case/orP => [ /eqP | ] Hin.
    subst h.
    rewrite eqxx /=.
    apply foldl_leq_monotonic => acc str_t.
    by rewrite /f -addnA leq_addr.
  case: ifP => [ /eqP ? | Hh /=].
    subst h.
    rewrite /=.
    apply foldl_leq_monotonic => acc str_t.
    by rewrite /f -addnA leq_addr.
  by apply IH with i tg t'.
Qed.

End foldl_sizeof.

(** field address *)

Obligation Tactic := idtac.

Program Fixpoint field_address {g} a str (t : g.-typ) (l : g.-env) (_ : (str, t) \in l) :=
  match l with
    | nil => @False_rect nat _
    | hd :: tl =>
      match eq_comparable (str, t) hd with
        | left H => a
        | right H =>
          let new_a := sizeof hd.2 + padd (a + sizeof hd.2) (align (head (str, t) tl).2) in
            field_address (a + new_a) str t tl _
      end
  end.
Next Obligation.
move => g _ str t l Hl Hl2.
by rewrite -Hl2 in Hl.
Defined.
Next Obligation.
move=> g _ str t l Hl hd tl l_cons /= H _.
rewrite -l_cons in_cons in Hl.
case/orP : Hl; last by done.
by move/eqP.
Defined.

Lemma field_address_eq_foldl {g} s (t : g.-typ) : forall l a Hin,
  align (head (s, t) l).2 %| a ->
  field_address a s t l Hin =
  let f := fun a (h : string * g.-typ) => a + padd a (align h.2) + sizeof h.2 in
  let a' := foldl f a (take (seq.index (s, t) l) l) in
  a' + padd a' (align (nth (s, t) l (seq.index (s, t) l)).2).
Proof.
elim => // hd tl Hind a Hin Halign /=.
set x := eq_comparable _ _.
case: x => [Heq | Hneq].
- subst; rewrite eq_refl //= padd_0 //= ?addn0 //; apply align_gt0.
- set ob := eq_ind_r _ _ _.
  set ob' := ob _; generalize ob'; clear ob ob'; move => ob.
  set a' := a + _.
  have Halign': align (head (s, t) tl).2 %| a' by rewrite /a' addnA; apply padd_isdiv; apply align_gt0.
  have ->: hd == (s, t) = false.
    move: Hneq => /eqP Hneqb.
    rewrite eq_sym; by apply/negbTE.
  rewrite (Hind _ ob Halign') => //= {Hind}.
  rewrite (padd_0 _ _ _ Halign); last by apply align_gt0.
  rewrite addn0.
  set padd_sizeof := fun acc elt =>  acc + padd acc (align elt.2) + sizeof elt.2.
  set Align := align (nth (s, t) tl (seq.index (s, t) tl)).2.
  set Take := take _ _.
  set a'' := a + _.
  clear Hin.
  destruct tl; simpl in *; first by rewrite in_nil in ob.
  clear Hneq.
  case: (p =P (s, t)) => [Heq | Hneq].
  + move: Heq => /eqP Heqb.
    rewrite /Align /Take; clear Align Take; rewrite Heqb //=.
    rewrite (padd_0 _ _ _ Halign'); last by apply align_gt0.
    by rewrite addn0 /a'' /a' addnA.
  + rewrite /Align /Take; clear Align Take; have ->: p == (s, t) = false.
      move: Hneq => /eqP Hneqb.
      by apply/negbTE.
    rewrite /padd_sizeof {padd_sizeof} //=.
    set padd_sizeof := fun acc elt => acc + padd acc (align elt.2) + sizeof elt.2.
    rewrite !(padd_0 _ _ _ Halign'); last by apply align_gt0.
    rewrite addn0.
    set Take := take _ _.
    set Align := align (nth (s, t) tl (seq.index (s, t) tl)).2.
    move: Halign'.
    rewrite /a' /a'' {a' a''}.
    by nat_norm.
Qed.

Fixpoint fields_size_fp {g} a (l : g.-env) (ty: g.-typ) :=
  match l with
    | nil => a
    | hd :: tl =>
      let new_a := sizeof hd.2 + padd (a + sizeof hd.2) (align (head (""%string, ty) tl).2) in
      fields_size_fp (a + new_a) tl ty
  end.

Lemma fields_size_field_address {g} str (t : g.-typ) :
  forall l1 l2 a Hin, ~ (str, t) \in l1 ->
  field_address a str t (l1 ++ (str, t) :: l2) Hin = fields_size_fp a l1 t.
Proof.
elim => [l2 addr Hin _ | hd tl Hind l2 addr Hin Hnotin] /=.
- set x := eq_comparable _ _.
  by case: x.
- set x := eq_comparable _ _.
  case: x => [Heq | Hneq].
  + rewrite Heq in Hnotin.
    exfalso.
    apply Hnotin; rewrite in_cons; apply/orP; by left.
  + set ob := eq_ind_r _ _ _.
    set ob2 := ob _; move: ob2; clear ob; move => ob.
    rewrite Hind; last first.
      move => Hin'; apply Hnotin.
      rewrite in_cons; apply/orP; by right.
    congr (fields_size_fp (_ + (_ + padd _ _))).
    by destruct tl.
Qed.

Lemma field_address_eq {g} a n t (l : g.-env) H : field_address a n t ((n, t) :: l) H = a.
Proof. by rewrite /= eq_comparable_eq. Qed.

Lemma field_address_ge {g} str (t : g.-typ) : forall l a Hin,
  a <= field_address a str t l Hin.
Proof.
elim => // hd tl Hind a Hin /=.
set x := eq_comparable _ _.
case: x => [H | Hneq']; first by apply leqnn.
set ob := eq_ind_r _ _ _; move: ob => ob.
set a' := a + _.
apply leq_trans with a'.
by apply leq_addr.
by apply Hind.
Qed.

Obligation Tactic := Tactics.program_simpl.

Program Definition field_address_slide1_statement :=
  forall g a str t str' t' (l : g.-env) H
  (K : (str, t) <> (str', t')),
  field_address a str t ((str', t')::l) H =
  field_address (a + sizeof t' + padd (a + sizeof t') (align (head (str, t) l).2))
    str t l _ .
Next Obligation.
move: H; rewrite inE; move/orP => []; last by done.
by move/eqP.
Defined.

Lemma field_address_slide1 : field_address_slide1_statement.
Proof.
rewrite /field_address_slide1_statement.
move=> g a str ty str' ty' l Hin Hneq /=.
set x := eq_comparable _ _.
case: x => [H | Hneq'].
- exfalso.
  by rewrite H in Hneq.
- set x := eq_ind_r _ _ _.
  set y := field_address_slide1_statement_obligation_1 _ _ _ _ _ _ _ _.
  rewrite !addnA.
  suff : x Hin = y by move=> ->.
  by apply/eq_irrelevance.
Qed.

Lemma field_address_slide {g} : forall l a b str (ty : g.-typ) H ,
  (forall i, i < size l -> forall str_dummy ty_dummy, (str_dummy, ty_dummy) \in l ->
    align (nth (str_dummy, ty_dummy) l i).2 %| a) ->
  field_address (a + b) str ty l H = a + field_address b str ty l H.
Proof.
elim=> //; case=> str' t' tl IH a b str t H Hali.
case: (eq_comparable str str') => [ | Hneq].
- move=> ?; subst str'.
  case : (eq_comparable t t') => [ | Hneq].
  + move=> ?; subst t'.
    by rewrite 2!field_address_eq.
  + rewrite field_address_slide1; first by case=> ?; subst.
    move=> Hneq'.
    rewrite field_address_slide1 -!addnA IH; last first.
      move=> i Hi str_dummy ty_dummy Hl.
      move: (Hali i.+1) => /=.
      rewrite ltnS.
      move/(_ Hi) => {Hali}Hali.
      apply Hali.
      by rewrite in_cons Hl orbC.
    rewrite padd_add //.
    move: (Hali 1); apply.
    * rewrite /=.
      destruct tl => //=.
      rewrite inE in H.
      by move/eqP in H.
    * by rewrite in_cons.
- rewrite field_address_slide1; first by case=> ?; subst.
  move=> Hneq'.
  rewrite field_address_slide1 -!addnA IH; last first.
    move=> i Hi str_dummy ty_dummy Hl.
    move: (Hali i.+1) => /=.
    rewrite ltnS.
    move/(_ Hi) => {Hali}Hali.
    apply Hali.
    by rewrite in_cons Hl orbC.
  rewrite padd_add //.
  move: (Hali 1%nat); apply.
  * rewrite /=.
    destruct tl => //=.
    rewrite inE in H.
    by move/eqP in H.
  * by rewrite in_cons.
Qed.

Lemma field_address_slide0 {g} l a str (t : g.-typ) H :
  (forall i, i < size l ->
    forall str0 t0, (str0, t0) \in l ->
      align (nth (str0, t0) l i).2 %| a) ->
  field_address a str t l H = a + field_address 0 str t l H.
Proof. move=> Hi; by rewrite -{1}(addn0 a) field_address_slide. Qed.

Lemma lt_field_address0_sizeof {g} : forall l (t' : g.-typ) tg
  (t'tg : Ctyp.ty _ t' = styp tg) str (t : g.-typ) Hin,
  l = get_fields g tg ->
  field_address 0 str t l Hin < sizeof t'.
Proof.
elim=> // h t IH ty' tg ty'_tg str ty Hin Hl.
rewrite (field_address_eq_foldl _ _ _ _ Hin); last by apply dvdn0.
rewrite /= (sizeof_foldl g ty' tg ty'_tg) /= foldl_map /=.
rewrite in_cons in Hin.
case/orP : Hin => Hin.
  move/eqP in Hin; subst h.
  rewrite eqxx /= padd0n addn0 addn_gt0 foldl_ltn_monotonic //.
  - move=> acc x.
    rewrite -[in X in leq X _](addn0 acc) -addnA ltn_add2l.
    by rewrite addn_gt0 sizeof_gt0 orbC.
  - by rewrite -Hl.
case: ifP => //.
  move/eqP => ?; subst h.
  (* same as above *)
  rewrite /= padd0n addn0 addn_gt0 foldl_ltn_monotonic //.
  - move=> acc x.
    rewrite -[in X in leq X _](addn0 acc) -addnA ltn_add2l.
    by rewrite addn_gt0 sizeof_gt0 orbC.
  - by rewrite -Hl.
move/eqP => H.
rewrite -Hl /= padd0n addn0 add0n.
refine (ltn_foldl_foldl _ _ (seq.index (str, ty) t) _ (str, ty) Hin _ ty') => //.
by rewrite index_mem.
Qed.

Section leq_field_address.

Context {g : wfctxt}.
Let f := fun a (h : string * g.-typ) => a + padd a (align h.2) + sizeof h.2.

Lemma leq_field_address_foldl : forall l (t' : g.-typ) tg
  (t'tg : Ctyp.ty _ t' = styp tg) str (t : g.-typ) Hin,
  l = get_fields g tg ->
  forall a, align (head (str, t) l).2 %| a ->
    field_address a str t l Hin + sizeof t <= foldl f a l.
Proof.
case=> // h t t' tg t'_tg str ty Hin Hl a Halign.
rewrite (field_address_eq_foldl _ _ _ _ Hin) //=.
move: Hin; rewrite in_cons; case/orP => [/eqP|] Hin.
  subst h.
  rewrite eqxx /=.
  apply foldl_leq_monotonic => acc Hacc.
  by rewrite /f -addnA leq_addr.
case: ifP => [/eqP ? | ].
- subst h.
  apply foldl_leq_monotonic => acc Hacc.
  by rewrite /f -addnA leq_addr.
- move/eqP => H /=.
  apply: (leq_foldl_foldl _ _ (seq.index (str, ty) t) _ _ _ _ _ tg t') => //.
  by rewrite index_mem.
Qed.

Lemma leq_field_address0_foldl l (t' : g.-typ) tg
  (t'_tg : Ctyp.ty _ t' = styp tg) str (t : g.-typ) Hin :
  l = get_fields g tg ->
  field_address 0 str t l Hin + sizeof t <= foldl f 0 l.
Proof. move=> Hl. by apply leq_field_address_foldl with t' tg. Qed.

End leq_field_address.

Lemma leq_field_address0_sizeof {g} l (t': g.-typ) tg
  (t'tg : Ctyp.ty _ t' = styp tg) str (t : g.-typ) Hin :
  l = get_fields g tg ->
  field_address 0 str t l Hin + sizeof t <= sizeof t'.
Proof.
move=> Hl.
rewrite /= (sizeof_foldl g _ _ t'tg) /= foldl_map /=.
eapply leq_trans; last by apply leq_addr.
subst l.
by eapply leq_field_address0_foldl; eauto.
Qed.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import ZArith_ext String_ext ssrnat_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_seplog C_pp.

Local Open Scope C_types_scope.
Local Open Scope string_scope.

Definition _Clst := "Clst".
Definition _data := "data".
Definition _next := "next".
Definition Clst_tg := mkTag _Clst.
Definition Clst_flds := (_data, ityp uint) :: (_next, ptyp (styp Clst_tg)) :: nil.

Definition _ret := "ret".
Definition _rem := "rem".
Definition _i := "i".

Module C_reverse_list_env <: CENV.
Definition g := \wfctxt{ _Clst |> Clst_flds \, \O \}.
Definition Clst := g.-typ: (styp Clst_tg).
Definition sigma : g.-env := (_i, :* Clst) :: (_ret, :* Clst) :: (_rem, :* Clst) :: nil.
Definition uniq_vars : uniq (unzip1 sigma) := Logic.eq_refl.
End C_reverse_list_env.

Definition g := C_reverse_list_env.g.
Definition sigma := C_reverse_list_env.sigma.
Definition Clst := C_reverse_list_env.Clst.

Eval compute in (sizeof Clst).

Module Import C_Seplog_m := C_Pp_f C_reverse_list_env.

Definition __i := %_i.
Definition __ret := %_ret.
Definition __rem := %_rem.

Local Open Scope C_cmd_scope.

Definition reverse_list :=
  _ret <- NULL ;
  While (\~b \b __i \= NULL) {{
    _rem <-* __i &-> _next;
    __i &-> _next *<- __ret ;
    _ret <- __i ;
    _i <- __rem }}.

Definition list_header (elt : int 32) (nextp : int ptr_len) : logs ((_data, ityp: uint) :: (_next, :* Clst) :: nil).
apply cons_logs => //=.
- apply log_of_uint.
  reflexivity.
  exact elt.
- apply cons_logs.
    apply log_of_ptr with (t' := g.-typ: styp Clst_tg).
    reflexivity.
  exact nextp.
- apply nil_logs.  
Defined.

Definition mk_cell (data : int 32) (next : int ptr_len) : Clst.-log := 
  log_of_styp Clst _ Logic.eq_refl (list_header data next).

Inductive seplogClst : seq (int 32) -> (:* Clst).-phy -> assert :=
| list_nil : forall s, seplogClst nil pv0 s hp.emp
| list_cons : forall s h t h1 h2, h1 # h2 ->
  forall a p, a <> pv0 ->
    (a |lV~> mk_cell h (ptr<=phy p)) s h1 ->
    seplogClst t p s h2 ->
    seplogClst (h :: t) a s (h1 \U h2).

Inductive sepClst : seq (int 32) -> (:* Clst).-phy -> assert :=
| lnil : forall s, sepClst nil pv0 s hp.emp
| lcons : forall hd tl a p, a <> pv0 ->
  ((a |lV~> mk_cell hd (ptr<=phy p)) ** sepClst tl p) ===> sepClst (hd :: tl) a.

Lemma sepClst_ind_new
     : forall P : seq (int 32) -> (:* Clst).-phy -> store -> heap -> Prop,
       (forall s : store, P nil pv0 s hp.emp) ->
       (forall (hd : int 32) (tl : seq (int 32)) (a p : (:* Clst).-phy),
        a <> pv0 ->
        forall (s : store) (h1 h2 : heap),
          h1 # h2 ->
        P tl p s h2 ->
        (a |lV~> mk_cell hd (ptr<=phy p)) s h1 ->
        (sepClst tl p) s h2 ->
        P (hd :: tl) a s (h1 \U h2)) ->
       forall (l : seq (int 32)) (p : (:* Clst).-phy) (s : store) (h : heap),
       sepClst l p s h -> P l p s h.
Proof.
fix 8.
intros.
destruct H1.
  apply H.
case: H2 => h1 h2 h1dh2 Hh1 Hh2.
apply H0 with p => //.
by apply sepClst_ind_new.
Qed.

Lemma sepClst_equiv l pv s h : seplogClst l pv s h <-> sepClst l pv s h.
Proof.
split.
  induction 1.
    by constructor.
  apply (lcons h t _ p H0 s (h1 \U h2)).
  by apply con_c.
induction 1 using sepClst_ind_new.
  by constructor.
  by apply list_cons with p.
Qed.

Lemma seplogClst_inde v l s s' h : seplogClst l v s h -> seplogClst l v s' h.
Proof.
elim => //=.
- move => ?; by constructor.
- move => *; by econstructor; eauto.
Qed.

Definition seplogClst_e (l : seq (int 32)) (e : exp sigma (:* Clst)) : assert :=
  fun s h => seplogClst l [ e ]_ s s h.

Module ppr_test.

Eval compute in (sizeof (g.-typ: (styp Clst_tg))).

Eval compute in
  (typ_to_string_rec g (g.-typ: (styp Clst_tg)) "l" "")%string.
Eval compute in
  (typ_to_string_rec g (g.-typ: (ptyp (ityp uint))) "var" "")%string.

Axiom PrintAxiom : forall A, A -> Set.

Goal phyval_to_string g (g.-typ: (styp Clst_tg))
    (map (Z2u 8) (0 :: 0 :: 0 :: 127 :: 0 :: 0 :: 0 :: 0 :: nil)) ""
  = "{127u, NULL}"%string.
Proof.
  compute -[pp_Z append Z.add Z.sub Z.mul].
  by rewrite !Z2uK.
Qed.

Goal PrintAxiom _
  (phyval_to_string g (g.-typ: (styp Clst_tg))
    (map (Z2u 8) (0 :: 0 :: 0 :: 127 :: 0 :: 0 :: 0 :: 0 :: nil)) "").
Proof.
  compute -[pp_Z append Z.add Z.sub Z.mul].
  rewrite !Z2uK //=; compute.
Abort.

Eval compute in pp_ctxt.
Eval compute in (foldl
  (fun s p => s ++ typ_to_string (C_types.Ctyp.ty _ (snd p)) (fst p) (line ";"))
  "" sigma).

Goal PrintAxiom _ (pp_cmd 0 reverse_list "").
  compute -[pp_Z append Z.add Z.sub Z.mul].
  rewrite !Z2uK //=.
Abort.

Goal pp_cmd 0 reverse_list "" = (
     line "ret = NULL;" ++
     line "while (!(((i) == (NULL)))) {" ++
     line "    rem = *(i)->next;" ++
     line "    *(i)->next = ret;" ++
     line "    ret = i;" ++
     line "    i = rem;" ++
     line "}")%string.
Proof.
  compute -[pp_Z append Z.add Z.sub Z.mul].
  rewrite !Z2uK /=.
  done.          
  done.
Qed.

End ppr_test.

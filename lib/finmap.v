(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Classical Permutation Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import seq_ext.
Require Import order ordset ordset_pairs uniq_tac.

(**********************************************************************************)
(* This file provides                                                             *)
(* - a module type (MAP) for finite maps (equality is the Coq equality)           *)
(* - a functor to instantiate finite maps between any ordered type and any eqtype *)
(* - a functor (Map_prop) with some additional, derived properties                *)
(* - a functor (MapTac) with some tactics                                         *)
(**********************************************************************************)

Reserved Notation "k '#' m" (at level 79, format "k  '#'  m").
Reserved Notation "k '\U' m" (at level 69, format "k  '\U'  m").
Reserved Notation "k '\D\' m" (at level 69, format "k  '\D\'  m").
Reserved Notation "k '|P|' m" (at level 69, format "k  '|P|'  m").
Reserved Notation "k '\I' m" (at level 79, format "k  '\I'  m").
Reserved Notation "k '\d\' l" (at level 69, format "k  '\d\'  l").

Module Type MAP.

Parameter l : eqType.
Parameter ltl : l -> l -> bool.
Parameter v : eqType.

Parameter t : Type.
Parameter elts : t -> seq (l * v).
Parameter dom : t -> seq l.
Parameter dom_ord : forall h, OrderedSequence.orderedb ltl (dom h).
Parameter cdom : t -> seq v.
Parameter size_cdom_dom : forall h, size (cdom h) = size (dom h).
Parameter elts_dom : forall d, map (fun x => fst x) (elts d) = dom d.
Parameter elts_cdom : forall d, map (fun x => snd x) (elts d) = cdom d.
Parameter dom_cdom_heap : forall h1 h2, dom h1 = dom h2 -> cdom h1 = cdom h2 -> h1 = h2.

(** empty map *)
Parameter emp : t.
Parameter dom_emp : dom emp = [::].
Parameter dom_emp_inv : forall k, dom k = [::] -> k = emp.
Parameter cdom_emp : cdom emp = [::].
Parameter elts_emp : elts emp = [::].

(** singleton map *)
Parameter sing : l -> v -> t.
Parameter elts_sing : forall n w, elts (sing n w) = [:: (n, w)].
Parameter dom_sing : forall n z, dom (sing n z) = [:: n].
Parameter cdom_sing : forall n z, cdom (sing n z) = [:: z].

Parameter sing_inj : forall n v1 v2, sing n v1 = sing n v2 -> v1 = v2.
(** retrieve an element *)
Parameter get : l -> t -> option v.
Parameter get_Some_in : forall k n w, get n k = Some w -> (n, w) \in elts k.
Parameter get_None_notin : forall k n, get n k = None -> n \notin dom k.
Parameter notin_get_None : forall k n, n \notin dom k -> get n k = None.
Parameter get_Some_in_dom : forall k n z, get n k = Some z -> n \in dom k.
Parameter in_dom_get_Some : forall k n, n \in dom k -> exists z, get n k = Some z.
Parameter get_Some_in_cdom: forall k n z, get n k = Some z -> z \in cdom k.
Parameter get_emp : forall x, get x emp = None.
Parameter get_sing : forall n w, get n (sing n w) = Some w.
Parameter get_sing_inv : forall n w n' w', get n (sing n' w') = Some w -> n = n' /\ w = w'.

Parameter extensionality : forall h1 h2, (forall x, get x h1 = get x h2) -> h1 = h2.
Parameter permut_eq : forall h1 h2, Permutation (elts h1) (elts h2) -> h1 = h2.

Parameter is_emp : t -> bool.
Parameter empP : forall h, reflect (h = emp) (is_emp h).

(** update an entry *)
Parameter upd : l -> v -> t -> t.
Parameter upd_sing : forall n w w', upd n w' (sing n w) = sing n w'.
Parameter get_upd : forall x y z st, x != y -> get x (upd y z st) = get x st.
Parameter get_upd_in : forall x z st, x \in dom st -> get x (upd x z st) = Some z.
Parameter upd_emp : forall l v, upd l v emp = emp.
Parameter upd_invariant : forall k p w, p \notin dom k -> upd p w k = k.
Parameter dom_upd_invariant : forall k n w, dom (upd n w k) = dom k.

(** disjointness *)
Parameter disj : t -> t -> Prop.
Local Notation "k '#' m" := (disj k m).

Parameter disjE : forall h1 h2, (h1 # h2) = dis (dom h1) (dom h2).
Parameter disj_sym : forall h0 h1, h0 # h1 -> h1 # h0.
Parameter disjhe : forall h, h # emp.
Parameter disjeh : forall h, emp # h.
Parameter disj_sing : forall x y z z', x != y -> sing x z # sing y z'.
Parameter disj_sing' : forall x y z z', sing x z # sing y z' -> x != y.
Parameter disj_sing_R : forall h n z, n \notin dom h -> h # sing n z.
Parameter disj_upd : forall n z h1 h2, h1 # h2 -> upd n z h1 # h2.
Parameter disj_same_dom : forall k1 k2 k2', k1 # k2' -> dom k2 = dom k2' -> k1 # k2.

Parameter add : l -> v -> t -> t.
Parameter size_add: forall n w k, (size (dom (add n w k)) <= (size (dom k)).+1)%nat.
Parameter get_add_eq : forall k n w, get n (add n w k) = Some w.
Parameter get_add_neq : forall k n w n', n != n' -> get n' (add n w k) = get n' k.
Parameter in_dom_add: forall k n n' w, n \in dom (add n' w k) = (n == n') || (n \in dom k).
Parameter add_eq_in_dom : forall k n w, n \in dom (add n w k).
Parameter add_neq_notin_dom: forall k n n' w, n != n' -> n \in dom (add n' w k) -> n \in dom k.

(** union *)
Parameter union : t -> t -> t.
Local Notation "k '\U' m" := (union k m).

Parameter unionhe : forall h, h \U emp = h.
Parameter unioneh : forall h, emp \U h = h.
Parameter unionC : forall h1 h2,  h1 # h2 -> h1 \U h2 = h2 \U h1.
Parameter in_dom_union_L : forall x h1 h2, x \in dom h1 -> x \in dom (h1 \U h2).
Parameter in_cdom_union_inv : forall t a b, t \in cdom (a \U b) -> t \in cdom a \/ t \in cdom b.
Parameter in_dom_union_inv : forall t a b, t \in dom (a \U b) -> t \in dom a \/ t \in dom b.
Parameter unionA : forall h1 h2 h3, h1 \U (h2 \U h3) = (h1 \U h2) \U h3.
Parameter get_union_sing_eq : forall x z st, get x (sing x z \U st) = Some z.
Parameter get_union_sing_neq : forall x y z st, x <> y -> get x (sing y z \U st) = get x st.
Parameter get_union_Some_inv : forall h1 h2 n z,
  get n (h1 \U h2) = Some z -> get n h1 = Some z \/ get n h2 = Some z.
Parameter get_union_L : forall h1 h2, h1 # h2 -> forall n z, get n h1 = Some z -> get n (h1 \U h2) = Some z.
Parameter get_union_R : forall h1 h2, h1 # h2 -> forall n z, get n h2 = Some z -> get n (h1 \U h2) = Some z.
Parameter get_union_None_inv : forall h1 h2 n, get n (h1 \U h2) = None -> get n h1 = None /\ get n h2 = None.
Parameter upd_union_L : forall h1 h2, h1 # h2 ->
  forall n z z1, get n h1 = Some z1 -> upd n z (h1 \U h2) = upd n z h1 \U h2.
Parameter upd_union_R : forall h1 h2, h1 # h2 ->
  forall n z z2, get n h2 = Some z2 -> upd n z (h1 \U h2) = h1 \U upd n z h2.
Parameter elts_union_sing : forall h n w, lb ltl n (dom h) ->
  elts (sing n w \U h) = (n, w) :: elts h.
Parameter dom_union_sing : forall h n w, lb ltl n (dom h) ->
  dom (sing n w \U h) = n :: dom h.
Parameter cdom_union_sing : forall k (a : l) b, lb ltl a (dom k) ->
  cdom (sing a b \U k) = b :: cdom k.
Parameter cdom_union : forall h1 h2,
  (forall i j, i \in dom h1 -> j \in dom h2 -> ltl i j) ->
  cdom (h1 \U h2) = cdom h1 ++ cdom h2.
Parameter dom_union : forall h1 h2,
  (forall i j, i \in dom h1 -> j \in dom h2 -> ltl i j) ->
  dom (h1 \U h2) = dom h1 ++ dom h2.
Parameter sing_union_sing : forall x v1 v2, sing x v1 \U sing x v2 = sing x v1.

Parameter Permutation_dom_union : forall h1 h2, h1 # h2 ->
  Permutation (dom (h1 \U h2)) (dom h1 ++ dom h2).
Parameter union_emp_inv : forall h1 h2, emp = h1 \U h2 -> h1 = emp /\ h2 = emp.
Parameter union_inv : forall h0 h0' h1 h2, h0 \U h1 = h0' \U h2 -> dom h0 = dom h0' -> h1 # h0 -> h2 # h0' -> h0 = h0' /\ h1 = h2.

Parameter disjhU : forall h1 h2 h0, h0 # h1 -> h0 # h2 -> h0 # h1 \U h2.
Parameter disjUh : forall h1 h2 h0, h1 # h0 -> h2 # h0 -> h1 \U h2 # h0.
Parameter disj_union_inv : forall h1 h2 h0, h0 # (h1 \U h2) -> h0 # h1 /\ h0 # h2.
Parameter dis_dom_union : forall h1 h2 l,
  dis l (dom (h1 \U h2)) = dis l (dom h1) && dis l (dom h2).
(* TODO: relation with elts_union_singl? *)
Parameter elts_union_sing_Perm : forall l d x rx,
  Permutation l (elts d) ->
  ~ List.In x (unzip1 l) ->
  Permutation ((x, rx) :: l) (elts (union (sing x rx) d)).

(** delete several entries *)
Parameter difs : t -> seq l -> t.
Local Notation "k '\D\' m" := (difs k m).

Parameter dis_difs : forall s l, dis (dom s) l -> s \D\ l = s.
Parameter difs_union : forall h1 h2 k, (h1 \U h2) \D\ k = (h1 \D\ k) \U (h2 \D\ k).
Parameter difs_union_L : forall h1 h2 k, dis (dom h2) k -> (h1 \U h2) \D\ k = (h1 \D\ k) \U h2.
Parameter difs_union_R : forall h1 h2 k, dis (dom h1) k -> (h1 \U h2) \D\ k = h1 \U (h2 \D\ k).
Parameter difs_self : forall k, k \D\ dom k = emp.

Parameter difs_upd : forall k n w d, n \in d -> upd n w k \D\ d = k \D\ d.
Parameter disj_difs : forall h1 h2, h1 # h2 -> forall d, h1 # h2 \D\ d.
Parameter disj_difs' : forall h1 h2 d, inc (dom h1) d -> h1 # h2 \D\ d.
Parameter get_difs : forall k x d, x \notin d -> get x (k \D\ d) = get x k.
Parameter get_difs_None : forall k x d, x \in d -> get x (k \D\ d) = None.
Parameter dom_difs_del : forall k d, dom (k \D\ d) = filter (predC (mem d)) (dom k).
Parameter mem_dom_difs : forall l x k, x \in dom l -> x \notin k -> x \in dom (l \D\ k).
Parameter difsK : forall s l, s \D\ l \D\ l = s \D\ l.
Parameter union_sing_difs : forall x v s, sing x v \U (s \D\ [:: x]) = sing x v \U s.

(** projection *)
Parameter proj : t -> seq l -> t.
Local Notation "k '|P|' m" := (proj k m).

Parameter proj_emp : forall l, emp |P| l = emp.
Parameter proj_nil : forall k, k |P| [::] = emp.
Parameter proj_proj : forall h d d', inc d' d -> (h |P| d) |P| d' = h |P| d'.
Parameter dom_proj_sing : forall k n, n \in dom k -> dom (k |P| [:: n]) = [:: n].
Parameter cdom_proj_sing : forall (k : t) (n : l) v, get n k = Some v ->
  cdom (k |P| [:: n]) = [:: v].
Parameter inc_dom_proj : forall d k, inc (dom (k |P| d)) d.
Parameter inc_dom_proj_dom : forall h d, inc (dom (h |P| d)) (dom h).
Parameter dom_proj_exact : forall h d, OrderedSequence.ordered ltl d -> inc d (dom h) -> dom (h |P| d) = d.
Parameter size_dom_proj_exact : forall h d, uniq d -> inc d (dom h) -> size (dom (h |P| d)) = size d.
Parameter dom_proj_cons : forall k n d, n \notin dom k -> k |P| (n :: d) = k |P| d.
Parameter in_dom_proj : forall x d h, x \in d -> x \in dom h -> x \in dom (h |P| d).
Parameter in_dom_proj_inter : forall k d m, m \in dom (k |P| d) -> m \in dom k /\ m \in d.
Parameter proj_upd : forall d k p w, upd p w k |P| d = upd p w (k |P| d).
Parameter get_proj : forall d k n, n \in d -> get n (k |P| d) = get n k.
Parameter get_proj_None : forall d k n, n \notin d -> get n (k |P| d) = None.
Parameter disj_proj_emp : forall h1 h2, h1 # h2 -> h1 |P| dom h2 = emp.
Parameter disj_proj_same_dom : forall k1 k2 d1 d2, dom k1 = dom k2 -> k1 |P| d1 # k1 |P| d2 -> k2 |P| d1 # k2 |P| d2.
Parameter dis_disj_proj : forall k1 k2 d1 d2, dis d1 d2 -> k1 |P| d1 # k2 |P| d2.
Parameter disj_proj_L : forall h d k, h # k -> h |P| d # k.
Parameter dom_dom_proj : forall h1 h2 d, dom h1 = dom h2 -> dom (h1 |P| d) = dom (h2 |P| d).
Parameter proj_itself : forall k, k |P| dom k = k.

Parameter proj_union_L : forall (h1 h2 : t) d, dis (dom h2) d -> (h1 \U h2) |P| d = h1 |P| d.
Parameter proj_union_L_dom : forall h h1 h2, h # h2 -> (h1 \U h2) |P| dom h = h1 |P| dom h.
Parameter proj_union_R_dom : forall h h1 h2, h # h1 -> (h1 \U h2) |P| dom h = h2 |P| dom h.
Parameter proj_app : forall k d1 d2, k |P| d1 ++ d2 = (k |P| d1) \U (k |P| d2).
Parameter proj_union_sing : forall k x y d, x \in d -> (sing x y \U k) |P| d = sing x y \U (k |P| d).
Parameter proj_union_sing_notin : forall k x y d, x \notin d -> (sing x y \U k) |P| d = k |P| d.
Parameter proj_dom_union : forall h h1 h2, h1 # h2 ->
  h |P| dom (h1 \U h2) = (h |P| dom h1) \U (h |P| dom h2).
Parameter proj_difs : forall k d, k = (k |P| d) \U (k \D\ d).
Parameter proj_difs_disj : forall k d d', inc d d' -> (k |P| d) # (k \D\ d').
Parameter proj_disj : forall k1 k2 k d, dom k1 = dom k2 -> k1 |P| k # d -> k2 |P| k # d.
Parameter cdom_proj_R : forall h l1 l2, dom h = l1 ++ l2 ->
  cdom (proj h l2) = drop (size l1) (cdom h).
Parameter cdom_difs : forall h l1 l2, dom h = l1 ++ l2 -> cdom (h \D\ l2) = take (size l1) (cdom h).
Parameter app_proj_difs : forall h l1 l2, dom h = l1 ++ l2 -> h |P| l1 = h \D\ l2.
Parameter app_proj_difs2 : forall h l1 l2, dom h = l2 ++ l1 -> h |P| l1 = h \D\ l2.
Parameter cdom_proj_L : forall h l1 l2, dom h = l1 ++ l2 ->
  cdom (h |P| l1) = take (size l1) (cdom h).

(** inclusion *)
Parameter inclu : t -> t -> Prop.
Local Notation "k '\I' m" := (inclu k m).

Parameter inclu_trans : forall h1 h2 h3, h1 \I h2 -> h2 \I h3 -> h1 \I h3.
Parameter incluE : forall h k, k \I h <-> h |P| dom k = k.
Parameter get_inclu : forall h1 h2,
  (forall n w, get n h1 = Some w -> get n h2 = Some w) -> h1 \I h2.
Parameter inclu_get : forall h1 h2, h1 \I h2 ->
  (forall n w, get n h1 = Some w -> get n h2 = Some w).
Parameter inclu_inc_dom : forall h1 h2, h1 \I h2 -> inc (dom h1) (dom h2).

(* NB move outside Parameter app_inclu : forall h1 h2 h3 h4, h1 # h2 -> h3 # h4 -> h1 # h3 -> h1 +++ h2 = h3 +++ h4 -> h3 [<=m] h2.*)

Parameter inclu_union_L : forall h1 h2 k, h1 # h2 -> k \I h1 -> k \I (h1 \U h2).
Parameter inclu_union_R : forall h1 h2 k, h1 # h2 -> k \I h2 -> k \I (h1 \U h2).

Parameter inclu_refl : forall k, k \I k.
Parameter proj_inclu : forall k h1 d, k \I (h1 |P| d) -> k \I h1.
Parameter get_inclu_sing : forall h a b, get a h = Some b -> sing a b \I h.
Parameter proj_restrict : forall h1 h2 d, h1 \I h2 -> inc d (dom h1) -> h2 |P| d = h1 |P| d.
Parameter union_difsK : forall h k d, k \I h -> dom k = d -> h = k \U (h \D\ d).
Parameter dom_union_difsK : forall h k, inc (dom k) (dom h) -> dom h = dom (k \U (h \D\ dom k)).
Parameter inclu_proj : forall h d, (h |P| d) \I h.
Parameter proj_dom_proj : forall k d, k |P| (dom (k |P| d)) = k |P| d.
Parameter inclu_difs : forall h d, (h \D\ d) \I h.
Parameter difs_difs : forall s x y, (s \D\ y) \D\ x = (s \D\ x) \D\ y.

Parameter disj_proj_inclu : forall h d1 k, h |P| d1 # k -> (h |P| d1) \I (h \D\ dom k).
Parameter incl_proj2 : forall h1 h2 k, h1 \I k -> h2 \I k ->
  dom h1 = dom h2 -> h1 = h2.
Parameter disj_proj_app : forall h k d1 d2, h # (k \D\ d1) ->
  h # (k \D\ d2) -> h # (k \D\ d1 ++ d2).

(** delete only one entry *)
Parameter dif : t -> l -> t.
Local Notation "k '\d\' l" := (dif k l).

Parameter difE : forall h n, h \d\ n = h \D\ [:: n].

Parameter size_dom_dif : forall a h, get a h != None -> (size (dom (h \d\ a)) < size (dom h))%nat.
Parameter dif_sing : forall a b, sing a b \d\ a = emp.
Parameter dif_emp : forall p, emp \d\ p = emp.
Parameter dif_union : forall h1 h2 a, (h1 \U h2) \d\ a = (h1 \d\ a) \U (h2 \d\ a).
Parameter dif_disj : forall h a b, h # sing a b -> h \d\ a = h.
Parameter dif_disj' : forall h1 h2 l, h1 # h2 -> (h1 \d\ l) # (h2 \d\ l).
Parameter get_dif : forall w st, get w (st \d\ w) = None.
Parameter get_dif' : forall st x y, x <> y -> get x (st \d\ y) = get x st.
Parameter proj_dif : forall k x d, x \in d -> (k \d\ x) |P| d = (k |P| d) \d\ x.

(* prove that a list of pairs is a permutation of a finmap *)
Ltac Permutation_list_elts :=
  repeat
    match goal with
      | |- Permutation (cons (?x, ?rx) _) (elts (union (sing ?r ?rx) _)) =>
        apply elts_union_sing_Perm; last by unfold unzip1; simpl seq.map; Uniq_not_In
      | |- Permutation (cons (?x, ?rx)  _) (elts (sing ?r ?rx)) =>
        rewrite -> elts_sing; simpl; by apply Permutation_refl
    end.

Ltac map_to_lst l :=
  match l with
    | union (sing ?r ?rx) ?tl =>
      let tl' := map_to_lst tl in
      constr: (cons (r, rx) tl')
    | sing ?r ?rx => constr: (cons (r, rx) nil)
  end.

(* generate for a cdom in the goal its codomain as a list *)
Ltac From_cdom_to_list H :=
  match goal with
    |- context ctxt_id [(cdom ?fima)] =>
      let fima_list := map_to_lst fima in
      let cdom_list := constr: (seq.map (fun x => snd x) fima_list) in
      assert (H : Permutation cdom_list (cdom fima)) ; [
        apply Permutation_trans with (seq.map (fun x : l * v => snd x) (elts fima)) ; [
          apply Permutation_map ;
          by Permutation_list_elts
        |
          by rewrite -> elts_cdom; apply Permutation_refl ]
      |
        idtac ]
  end.

(* generate for a dom in the goal its domain as a list *)
Ltac From_dom_to_list H :=
  match goal with
    |- context ctxt_id [(dom ?fima)] =>
      let fima_list := map_to_lst fima in
      let dom_list := constr: (seq.map (fun x => fst x) fima_list) in
      assert (H : Permutation dom_list (dom fima)) ; [
        apply Permutation_trans with (seq.map (fun x : l * v => fst x) (elts fima)) ; [
          apply Permutation_map ;
          by Permutation_list_elts
        |
          by rewrite -> elts_dom; apply Permutation_refl ]
      |
        idtac ]
  end.

Ltac Permutation_elts_elts :=
  match goal with
    |- Permutation (elts ?fima) (elts ?fima2) =>
      let fima_list := map_to_lst fima in
      let fima_list2 := map_to_lst fima2 in
        apply Permutation_trans with fima_list ;
          [ apply Permutation_sym ;
            Permutation_list_elts
            |
            apply Permutation_trans with fima_list2 ;
              [ seq_ext.PermutProve
                |
                Permutation_list_elts
              ]
          ]
  end.

Ltac Equal_union :=
  match goal with
    | |- union _ _ = union _ _ =>
      apply permut_eq ;
      Permutation_elts_elts
  end.

End MAP.

Module Type EQTYPE.
  Parameter A : eqType.
End EQTYPE.

(* computational version of map *)
Module compmap (X : ORDER) (E : EQTYPE) <: MAP
  with Definition l := X.A
    with Definition v := E.A
      with Definition ltl := X.ltA.

Definition l := X.A.
Definition ltl := X.ltA.
Definition v := E.A.

Import OrderedSequence.

(** definition of maps *)

Inductive t' : Type := mk_t (k : seq (l * v)) of ordered X.ltA (unzip1 k).
Definition t := t'.

Definition elts (k : t) := let (lst, _) := k in lst.
Definition prf (k : t) := let (l, v) as h return ordered X.ltA (unzip1 (elts h)) := k in v.

Lemma mk_t_pi : forall l1 (H1 : ordered X.ltA (unzip1 l1)) l2 (H2 : ordered X.ltA (unzip1 l2)),
  l1 = l2 -> mk_t l1 H1 = mk_t l2 H2.
Proof.
move=> l1 H1 l2 H2 H; subst l2; by rewrite (proof_irrelevance _ H1 H2).
Qed.

Definition dom m := unzip1 (elts m).

Lemma dom_ord : forall h, OrderedSequence.orderedb ltl (dom h).
Proof. case=> h; by rewrite /dom /= => /orderedP. Qed.

Definition cdom m := unzip2 (elts m).

Lemma size_cdom_dom : forall h, size (cdom h) = size (dom h).
Proof.
case.
elim=> // hd tl IH /=.
case/ordered_inv=> H1 H2.
congr S.
move: (IH H1).
by rewrite /cdom /= => ->.
Qed.

Lemma elts_dom d : map (fun x => fst x) (elts d) = dom d. Proof. by []. Qed.

Lemma elts_cdom d : map (fun x => snd x) (elts d) = cdom d. Proof. by []. Qed.

Lemma dom_cdom_heap : forall h1 h2, dom h1 = dom h2 -> cdom h1 = cdom h2 -> h1 = h2.
Proof.
case=> [h1 H1] [h2 H2].
rewrite /dom /cdom /= => dom_12 cdom_12.
apply mk_t_pi.
by rewrite -(zip_unzip h1) -(zip_unzip h2) dom_12 cdom_12.
Qed.

Definition emp := mk_t [::] (ord_nil X.ltA).

Lemma dom_emp : dom emp = [::]. by []. Qed.

Lemma dom_emp_inv : forall k, dom k = [::] -> k = emp.
Proof. case=> /=;move=> [|lst] // ord _. by apply mk_t_pi. Qed.

Lemma cdom_emp : cdom emp = [::]. by []. Qed.

Lemma elts_emp : elts emp = [::]. by []. Qed.

Lemma ordered_sing : forall n (v : v), ordered X.ltA (unzip1 [:: (n, v)]).
Proof. move=> n w /=. by repeat constructor. Qed.

Definition sing n w := mk_t [:: (n, w)] (ordered_sing n w).

Lemma elts_sing : forall n w, elts (sing n w) = [:: (n, w)]. by []. Qed.

Lemma dom_sing : forall n z, dom (sing n z) = [:: n]. by []. Qed.

Lemma cdom_sing : forall n z, cdom (sing n z) = [:: z]. by []. Qed.

Lemma sing_inj : forall n v1 v2, sing n v1 = sing n v2 -> v1 = v2.
Proof. by move=> n v1 v2 []. Qed.

Definition get_seq (n : l) k : option v :=
  if ocamlfind (fun x => n == x.1) k is Some r then Some r.2 else None.

Lemma get_seq_cons : forall k a b, get_seq a ((a, b) :: k) = Some b.
Proof. move=> k a b. rewrite /get_seq. by rewrite ocamlfind_cons. Qed.

Lemma get_seq_cons' k a b n : a <> n -> get_seq n ((a, b) :: k) = get_seq n k.
Proof.
move=> H. rewrite {1}/get_seq ocamlfind_cons' //=. apply/negP. apply/eqP. auto.
Qed.

Lemma get_seq_Some_in : forall k n w, get_seq n k = Some w -> (n, w) \in k.
Proof.
elim=> //.
move=> [n w] tl IH n' w'.
case/boolP : (n == n') => [/eqP <- |X].
- rewrite get_seq_cons. case=> ->.
  by rewrite in_cons eqxx.
- rewrite get_seq_cons' //; last by apply/eqP.
  move/IH.
  rewrite in_cons => ->.
  by rewrite orbC.
Qed.

Lemma get_seq_Some_in_unzip1 k n z : get_seq n k = Some z -> n \in unzip1 k.
Proof. move/get_seq_Some_in => H. apply/mapP. by exists (n, z). Qed.

Lemma get_seq_Some_in_unzip2 k n z : get_seq n k = Some z -> z \in unzip2 k.
Proof. move/get_seq_Some_in => H. apply/mapP. by exists (n, z). Qed.

Lemma in_get_seq_Some : forall k n, n \in unzip1 k -> exists z, get_seq n k = Some z.
Proof.
elim=> [| [hd1 hd2] tl IH] // n /=.
rewrite in_cons; case/orP.
- move/eqP => X; subst. exists hd2; by apply get_seq_cons.
- case/IH => {IH} z X. case/boolP: (n == hd1) => [/eqP <- |].
  + exists hd2; by apply get_seq_cons.
  + move=> Y. exists z; rewrite get_seq_cons' //.
    apply/eqP. by rewrite eq_sym.
Qed.

Lemma ord_in_get_seq_Some : forall k n w, ordered X.ltA (unzip1 k) -> (n, w) \in k -> get_seq n k = Some w.
Proof.
elim=> // hd tl IH n w /=.
case/ordered_inv => H1 H2.
rewrite in_cons /=.
case/orP => X.
move/eqP : X => X; subst hd.
by rewrite get_seq_cons.
destruct hd as [hd1 hd2].
rewrite get_seq_cons'.
by apply IH.
move/(mem_lb X.ltA_irr) : H2.
rewrite /= => H3.
move=> Y; subst hd1.
move/mem_unzip1 : X.
by rewrite (negbTE H3).
Qed.

Lemma get_seq_None_notin : forall k n, get_seq n k = None -> ~ n \in unzip1 k.
Proof. move=> k n H. move/in_get_seq_Some. rewrite H. by case. Qed.

Definition get n k := get_seq n (elts k).

Lemma get_Some_in : forall k n w, get n k = Some w -> (n, w) \in elts k.
Proof. move=> [k Hk] /= n w H. by apply get_seq_Some_in. Qed.

Lemma get_None_notin : forall k n, get n k = None -> n \notin dom k.
Proof. move=> [k Hk] n. rewrite /get /=. move/get_seq_None_notin. by move/negP. Qed.

Lemma get_Some_in_dom : forall k n z, get n k = Some z -> n \in dom k.
Proof. move=> [k Hk] n z. rewrite /get /=. by apply get_seq_Some_in_unzip1. Qed.

Lemma notin_get_seq_None : forall k n, ~ n \in unzip1 k -> get_seq n k = None.
Proof.
move=> k n H. move z : (get_seq _ _) => [] //. move/get_seq_Some_in_unzip1; tauto.
Qed.

Lemma notin_get_None : forall k n, n \notin dom k -> get n k = None.
Proof.
move=> [k Hk] n.
rewrite /dom /= /get /= => H.
apply notin_get_seq_None.
exact/negP.
Qed.

Lemma in_unzip1_get_seq_Some : forall k n, n \in unzip1 k ->
  exists z, get_seq n k = Some z.
Proof.
elim => // hd tl IH n; rewrite /unzip1; case/mapP => x.
rewrite in_cons; case/orP.
- move/eqP => <- ->; exists x.2; by rewrite /get_seq /= eqxx.
- move=> Hx ->.
  have : x.1 \in map (fun x => fst x) tl.
    apply/mapP; by exists x.
  case/IH => y Hy.
  case/boolP : (x.1 == hd.1).
  + rewrite /get_seq /= => ->; by exists hd.2.
  + rewrite /get_seq /=; move/negbTE => ->; by exists y.
Qed.

Lemma in_dom_get_Some : forall k n, n \in dom k -> exists z, get n k = Some z.
Proof.
move=> [k Hk] n; rewrite /get /= /dom /= => Hn; by apply in_unzip1_get_seq_Some.
Qed.

Lemma get_Some_in_cdom : forall k n z, get n k = Some z -> z \in cdom k.
Proof. move=> [k Hk] n z. rewrite /get /=. by apply get_seq_Some_in_unzip2. Qed.

Lemma get_emp x : get x emp = None. Proof. by rewrite /get /get_seq. Qed.

Lemma get_sing : forall n w, get n (sing n w) = Some w.
Proof. move=> n w. by rewrite /sing /get get_seq_cons. Qed.

Lemma get_sing_inv : forall n w n' w', get n (sing n' w') = Some w -> n = n' /\ w = w'.
Proof.
move=> n w n' w'.
rewrite /get /sing /=.
case/boolP: (n == n') => [/eqP <-| X].
- rewrite get_seq_cons; by case=> ->.
- rewrite get_seq_cons' /=; last by move/eqP : X; auto.
  by rewrite /get_seq.
Qed.

(** map equivalence *)

Definition equal h1 h2 := elts h1 = elts h2.
Local Notation "k '\=' m" := (equal k m) (at level 79, format "k  '\='  m").

Lemma equal_eq : forall h1 h2, h1 \= h2 -> h1 = h2.
Proof.
move=> [l1 p1] [l2 p2]; rewrite /equal /=.
move=> *; subst. by rewrite (proof_irrelevance _ p1 p2).
Qed.

Lemma eq_equal: forall h1 h2, h1 = h2 -> h1 \= h2.
Proof. rewrite /equal; move=> *; subst => //=. Qed.

Ltac ord_pro := solve [apply X.ltA_trans | apply X.ltA_irr | apply X.ltA_total].

Lemma ext_helper : forall l1 l2,
  ordered X.ltA (unzip1 l1) -> ordered X.ltA (unzip1 l2) ->
  unzip1 l1 = unzip1 l2 ->
  (forall x, get_seq x l1 = get_seq x l2) ->
  l1 = l2.
Proof.
elim; first by case.
case=> x y tl IH /=; case => //= [[x' y'] tl'] /=.
case/ordered_inv => HA HB. case/ordered_inv => HC HD.
case=> X Y; subst x' => Hext.
move: (Hext x).
rewrite 2!get_seq_cons.
case=> Z; subst.
rewrite (IH tl') // => z.
move: (Hext z) => Z.
case/boolP: (z == x) => [/eqP|] U.
- subst.
  rewrite notin_get_seq_None; last first.
    move/(mem_lb X.ltA_irr): HB.
    by move/negP.
  rewrite notin_get_seq_None //.
  move/(mem_lb X.ltA_irr): HD.
  by move/negP.
- rewrite get_seq_cons' in Z; last first.
    apply/eqP; by rewrite eq_sym.
  rewrite get_seq_cons' // in Z.
  apply/eqP; by rewrite eq_sym.
Qed.

Lemma extensionality_seq l1 l2 :
  ordered X.ltA (unzip1 l1) -> ordered X.ltA (unzip1 l2) ->
  (forall x, get_seq x l1 = get_seq x l2) -> l1 = l2.
Proof.
move=> H1 H2 Hext.
apply: ext_helper => //.
apply: ordered_ext; try ord_pro||auto.
move=> x.
rewrite 2!has_pred1.
move: (Hext x) => X.
have [Y|Y] : (exists z, get_seq x l1 = Some z) \/ get_seq x l1 = None.
  case (get_seq x l1).
  move=> x'; left; by exists x'.
  by right.
- case : Y => z Z.
  rewrite Z in X; symmetry in X.
  rewrite (get_seq_Some_in_unzip1 _ _ _ Z) (get_seq_Some_in_unzip1 _ _ _ X) //.
- rewrite Y in X; symmetry in X.
  move/get_seq_None_notin : Y => /negP Y.
  move/get_seq_None_notin : X => /negP X.
  by rewrite (negbTE Y) (negbTE X).
Qed.

Lemma extensionality : forall h1 h2, (forall x, get x h1 = get x h2) -> h1 = h2.
Proof.
move=> [l1 H1] [l2 H2] H.
apply equal_eq.
have ? : l1 = l2 by apply extensionality_seq.
subst.
by rewrite (proof_irrelevance _ H1 H2).
Qed.

Lemma permut_eq : forall h1 h2, Permutation (elts h1) (elts h2) -> h1 = h2.
Proof.
move=> [h1 H1] [h2 H2] /= H.
apply extensionality => x.
rewrite /get /=.
move Hxy1 : (get_seq x h1) => [vv|].
- move Hxy2 : (get_seq x h2) => [w|].
  + move/get_seq_Some_in in Hxy2.
    move/get_seq_Some_in/inP/(Permutation_in _ H)/inP : Hxy1.
    move/(FinSetOfPairsForMap.in_inj X.ltA_irr h2 _ _ H2 Hxy2).
    by move/(_ (refl_equal _)) => ->.
  + move/get_seq_Some_in/inP/(Permutation_in _ H)/inP/mem_unzip1 in Hxy1.
    move/get_seq_None_notin in Hxy2.
    by rewrite Hxy1 in Hxy2.
- move Hxy2 : (get_seq x h2) => [s|] //.
  apply Permutation_sym in H.
  move/get_seq_Some_in/inP/(Permutation_in _ H)/inP/mem_unzip1 in Hxy2.
  move/get_seq_None_notin : Hxy1.
  by rewrite Hxy2.
Qed.

Definition is_emp h := elts h == [::].

Lemma empP : forall h, reflect (h = emp) (is_emp h).
Proof.
move=> [] [|h t] Hh; rewrite /is_emp /=.
- rewrite eqxx; by apply ReflectT, extensionality.
- rewrite (_ : h :: t == [::] = false) //; by apply ReflectF.
Qed.

Fixpoint upd_seq (n : l) (w : v) (k : seq (l * v)) { struct k } :=
  match k with
    | [::] => [::]
    | (h1, h2) :: tl => if n == h1 then (h1, w) :: tl else (h1, h2) :: upd_seq n w tl
  end.

Lemma size_upd_seq : forall k n w, size (upd_seq n w k) = size k.
Proof.
elim=> //; case=> h1 h2 tl IH n w /=; case: ifP => [ | /= nh1].
- move/eqP => ?; by subst h1.
- by rewrite IH.
Qed.

Lemma unzip1_upd_seq : forall k n w, unzip1 (upd_seq n w k) = unzip1 k.
Proof.
elim=> //=; case=> x1 x2 /= tl IH n w.
case: ifP => X //=; by rewrite IH.
Qed.

Lemma ocamlfind_upd_seq : forall k n w, n \in unzip1 k ->
  ocamlfind (fun x => n == x.1) (upd_seq n w k) = Some (n, w).
Proof.
elim=> [| [hd1 hd2] tl IH] /= n w //.
rewrite in_cons.
case/orP => X.
- rewrite /= X /= X //.
  by move/eqP : X => <-.
- case/boolP: (n == hd1) => /= Y.
  + by rewrite Y /= (eqP Y).
  + rewrite (negbTE Y) /=.
    by apply IH.
Qed.

Lemma ocamlfind_upd_seq' : forall k n w n',
  n <> n' -> n \in unzip1 k ->
  ocamlfind (fun x => n' == x.1) (upd_seq n w k) = ocamlfind (fun x => n' == x.1) k.
Proof.
elim=> [| [hd1 hd2] tl IH] n w n' /eqP H //=.
rewrite in_cons.
case/orP => [/eqP X | X].
- subst.
  by rewrite eq_refl /= eq_sym (negbTE H).
- case: ifP => [/eqP Y | /negbT Y /=].
  + subst.
    by rewrite /= eq_sym (negbTE H).
  + case: ifP => [/eqP Z // | /negbT Z].
    apply IH => //;  by apply/eqP.
Qed.

Lemma in_unzip1_in_upd_seq : forall k n w, n \in unzip1 k -> (n, w) \in upd_seq n w k.
Proof.
elim=> //=.
move=> [x1 x2] /= tl IH n w.
rewrite !in_cons; case/orP.
- move/eqP => ?; subst.
  by rewrite eq_refl /= !in_cons eq_refl.
- move=> X.
  case: ifP => [/eqP Y | /negbT nx1 /=].
  + subst.
    by rewrite /= !in_cons eq_refl.
  + by rewrite !in_cons IH // orbC.
Qed.

Lemma upd_seq_invariant : forall k n, ~ n \in unzip1 k -> forall z, upd_seq n z k = k.
Proof.
elim=> //=; case=> [h1 h2] /= tl IH n.
move/negP; move/norP => [H1 H2] z.
rewrite (negbTE H1) IH //.
by apply/negP.
Qed.

Lemma in_upd_seq_inv : forall k n w x, x \in upd_seq n w k -> x = (n, w) \/ x \in k.
Proof.
elim=> //; case=> h1 h2 /= tl IH n w x.
case: ifP => [/eqP X /= | nh1 ].
- subst.
  rewrite !in_cons; case/orP => [/eqP -> | ->].
  + by left.
  + rewrite orbC /=; by right.
- rewrite /= !in_cons; case/orP.
  + move=> ->; by right.
  + case/(IH _ _ _); first by left.
    move=> ->; rewrite orbC /=; by right.
Qed.

Lemma upd_seq_upd_seq_eq : forall k n w w', upd_seq n w (upd_seq n w' k) = upd_seq n w k.
Proof.
elim=> //=; case=> [h1 h2] /= tl IH n w w'.
case: ifP => [/eqP X /= | /negbT X].
- by rewrite X eqxx.
- by rewrite /= (negbTE X) IH.
Qed.

Lemma upd_seq_upd_seq_neq : forall k n n', n <> n' -> n \in unzip1 k -> n' \in unzip1 k ->
  forall w w', upd_seq n w (upd_seq n' w' k) = upd_seq n' w' (upd_seq n w k).
Proof.
elim=> //=; case=> [h1 h2] /= tl IH n n' Hnn'.
rewrite !in_cons; case/orP => X.
- move/eqP:X=>X; subst.
  case/orP => X.
  + move/eqP : X => X; subst. tauto.
  + have Y : h1 == n' = false by apply/eqP.
    by rewrite eq_sym Y /= eq_refl /= eq_sym Y.
- case/orP => Y.
  + move/eqP : Y => Y; subst.
    rewrite eq_refl /=.
    have Y : n == h1 = false by apply/eqP.
    by rewrite Y /= eq_refl.
  + case: (tri' X.ltA_total n' h1) => [Z| [Z|Z]].
    * rewrite (lt_neq X.ltA_total Z) /=.
      case: (tri' X.ltA_total n h1) => [W| [W|W]].
      - rewrite (lt_neq X.ltA_total W) /= (lt_neq X.ltA_total Z) /=.
        move=> w w'; by rewrite IH.
      - subst.
        by rewrite eq_refl /= (lt_neq X.ltA_total Z).
      - rewrite eq_sym (lt_neq X.ltA_total W) /= (lt_neq X.ltA_total Z) //=.
        move=> w w'; by rewrite IH.
    * subst.
      rewrite eq_refl /=.
      have Z : n == h1 = false by apply/eqP.
      by rewrite Z /= eq_refl.
    * rewrite eq_sym (lt_neq X.ltA_total Z) //=.
      case: (tri' X.ltA_total n h1) => [W| [W|W]].
      - rewrite (lt_neq X.ltA_total W) /= eq_sym (lt_neq X.ltA_total Z) /=.
        move=> w w'; by rewrite IH.
      - subst.
        by rewrite eq_refl /= eq_sym (lt_neq X.ltA_total Z).
      - rewrite eq_sym (lt_neq X.ltA_total W) //= eq_sym (lt_neq X.ltA_total Z) //=.
        move=> w w'; by rewrite IH.
Qed.

Lemma get_seq_upd_seq : forall k x y z, x <> y -> get_seq x k = get_seq x (upd_seq y z k).
Proof.
elim => [| [a b] l0 H] x y z Hxy => //=.
case: ifP => [/eqP X | X /=].
- subst.
  rewrite !get_seq_cons' //; by auto.
- case/boolP: (x == a) => [/eqP Hxa | Hxa].
  + subst.
    by do 2! rewrite get_seq_cons.
  + move/eqP in Hxa.
    do 2 (rewrite get_seq_cons'; last by auto).
    by apply H.
Qed.

(* NB:
Lemma get_seq_upd_seq_eq : forall (k : seq (prod_eqType l v)) (x : l) (z : v),
   get_seq x (upd_seq x z k) = Some z.
not provable (false for k = nil) *)

Lemma ordered_upd_seq k : ordered X.ltA (unzip1 k) -> forall n w, ordered X.ltA (unzip1 (upd_seq n w k)).
Proof. move=> H n w. by rewrite unzip1_upd_seq. Qed.

Definition upd n w k := mk_t (upd_seq n w (elts k)) (ordered_upd_seq (elts k) (prf k) n w).

Lemma upd_sing n w w' : upd n w' (sing n w) = sing n w'.
Proof. apply equal_eq; by rewrite /equal /= eq_refl. Qed.

Lemma get_upd x y z st : x != y -> get x (upd y z st) = get x st.
Proof. move=> ?; exact/esym/get_seq_upd_seq/eqP. Qed.

Lemma get_upd_in : forall x z st, x \in dom st -> get x (upd x z st) = Some z.
Proof.
move => x z [k Hk]; move: Hk; rewrite/dom/elts.
elim: k; [done | ].
move => [y w] rest IH; rewrite/upd; simpl; move => Hk xin; rewrite/get/elts.
case_eq (x == y).
- move/idP/eqP => xy; subst; rewrite/get_seq/ocamlfind => /=.
  have -> : y == y = true by apply/idP/eqP; done.
  done.
- move => xy; move: IH; rewrite/get/get_seq/ocamlfind; simpl; rewrite xy.
  move => IH; rewrite IH; [done | | ].
  - move: Hk; move => H; inversion H; assumption.
  - move: xin; rewrite in_cons; case/orP; [ rewrite xy; done | done ].
Qed.

Lemma upd_emp k w : upd k w emp = emp.
Proof. apply extensionality => /= x. by rewrite /get /upd. Qed.

Lemma upd_invariant : forall k p w, p \notin dom k -> upd p w k = k.
Proof.
case=> k Hk p w.
rewrite /upd /= => H.
apply mk_t_pi, upd_seq_invariant.
by apply/negP.
Qed.

Lemma unzip1_upd_seq_invariant : forall k n w, unzip1 (upd_seq n w k) = unzip1 k.
Proof.
elim=> //; case=> [hd1 hd2] tl /= IH n w.
case: ifP => X //=; by rewrite IH.
Qed.

Lemma dom_upd_invariant : forall k n w, dom (upd n w k) = dom k.
Proof.
move=> [k Hk] n w /=.
rewrite /dom /elts /=.
by apply unzip1_upd_seq_invariant.
Qed.

Definition disj h1 h2 : Prop := dis (unzip1 (elts h1)) (unzip1 (elts h2)).
Local Notation "k '#' m" := (disj k m).

Lemma disjE : forall h1 h2, (h1 # h2) = dis (dom h1) (dom h2). Proof. done. Qed.

Lemma disj_sym h1 h2 : h1 # h2 -> h2 # h1.
Proof. move=> ?; by apply/disP/disj_sym/disP. Qed.

Lemma disjhe h : h # emp.
Proof. by apply/disP/disj_nil_R. Qed.

Lemma disjeh h : emp # h.
Proof. exact/disP/seq_ext.disj_sym/disj_nil_R. Qed.

Lemma disj_sing x y z z' : x != y -> sing x z # sing y z'.
Proof. move/negbTE => x_y; by rewrite /disj /= in_cons x_y. Qed.

Lemma disj_sing' x y z z' : sing x z # sing y z' -> x != y.
Proof. by rewrite /disj /sing /= mem_seq1; case: ifPn. Qed.

Lemma disj_sing_R : forall h n z, n \notin dom h -> h # sing n z.
Proof.
case; elim => [/= o n z _| [n z] tl IH Ho n0 z0].
- by apply disjeh.
- rewrite /disj /=; case: ifP => [|_].
  + rewrite in_cons in_nil orbC /=; move/eqP => ?; subst n0.
    by rewrite /dom /= in_cons eqxx.
  + rewrite /dom /= in_cons /= negb_or dis_sym dis_cons /=.
    by case/andP => _ ->.
Qed.

Lemma disj_upd n z : forall h1 h2, h1 # h2 -> upd n z h1 # h2.
Proof. case=> h1 H1 [h2 H2] /=; rewrite /disj /upd /= => H. by rewrite unzip1_upd_seq. Qed.

Lemma disj_same_dom : forall k1 k2 k2', k1 # k2' -> dom k2 = dom k2' -> k1 # k2.
Proof.
move=> [k1 H1] [k2 H2] [k1' H1'].
rewrite /disj /dom /unzip1 /= => disj12' dom22'.
by rewrite dom22'.
Qed.

(** element addition *)

Import FinSetOfPairsForMap.

Definition add_seq n w k := if n \in unzip1 k then upd_seq n w k else add_map X.ltA n w k.

Lemma size_add_seq : forall k n w, ordered X.ltA (unzip1 k) ->
  (size (add_seq n w k) <= (size k).+1)%nat.
Proof.
elim=> //=; case=> h1 h2 /= t IH n w.
case/ordered_inv => tord h1_t.
rewrite /add_seq /unzip1 map_cons in_cons.
case: ifP => [ | /= ].
- case/orP.
  + move/eqP => ?; subst n => /=; by rewrite eqxx.
  + move=> Hn /=.
    have nh1 : n != h1.
      apply/eqP => ?; subst h1.
      apply mem_lb in h1_t; last by ord_pro.
      by rewrite Hn in h1_t.
    by rewrite (negbTE nh1) /= size_upd_seq.
- move/negbT.
  rewrite negb_or.
  case/andP => /= nh1 Hn.
  rewrite (negbTE nh1).
  case: ifP => nh1' //=.
  move: (IH n w tord).
  by rewrite /add_seq (negbTE Hn).
Qed.

Lemma ordered_add_seq k : ordered X.ltA (unzip1 k) -> forall n w,
  ordered X.ltA (unzip1 (add_seq n w k)).
Proof.
move=> Hk n w.
rewrite /add_seq.
case: ifP => H.
by apply ordered_upd_seq.
apply ordered_unzip1_add_map => //.
exact X.ltA_trans.
exact X.ltA_total.
exact X.ltA_irr.
by apply/negP/negbT.
Qed.

Definition add n w k := mk_t (add_seq n w (elts k)) (ordered_add_seq (elts k) (prf k) n w).

Lemma size_add n w : forall k, (size (dom (add n w k)) <= (size (dom k)).+1)%nat.
Proof. move=> [l ord_l]; by rewrite /add /= /dom /= !size_map size_add_seq. Qed.

Lemma lb_add_seq : forall lst n m w, lb X.ltA n (unzip1 lst) -> X.ltA n m ->
  lb X.ltA n (unzip1 (add_seq m w lst)).
Proof.
elim.
- by move=> n m w _ /= ->.
- case=> h1 h2 tl IH n m w /=.
  case/andP => n_h1 n_tl n_m.
  rewrite /add_seq /= in_cons /=.
  case: ifP.
  + case/orP.
    * move/eqP => ?; subst h1.
      by rewrite eqxx /= n_h1 n_tl.
    * move=> m_tl.
      case: ifP.
      - move/eqP => ?; subst h1.
        by rewrite /= n_h1 /=.
      - move/eqP => m_h1 /=.
        rewrite n_h1 /=.
        move: (IH n m w n_tl n_m).
        by rewrite /add_seq m_tl.
  + move/negbT.
    rewrite negb_or.
    case/andP=> m_h1 m_tl.
    case: ifP.
    * move=> m_h1_.
      by rewrite /= n_m /= n_h1 /=.
    * rewrite (negbTE m_h1) /=.
      move=> m_h1_.
      rewrite n_h1 /=.
      move: (IH n m w n_tl n_m).
      by rewrite /add_seq (negbTE m_tl).
Qed.

Lemma add_seq_is_cons k a b : lb X.ltA a (unzip1 k) -> add_seq a b k = (a, b) :: k.
Proof.
move=> H.
rewrite /add_seq (negbTE (mem_lb X.ltA_irr H)).
by apply (add_map_is_cons _ X.ltA _ k a b).
Qed.

Lemma add_seq_ub : forall k a b, ub X.ltA a (unzip1 k) -> add_seq a b k = k ++ (a, b) :: nil.
Proof.
elim=> //; case=> [n w] /= tl IH a b; case/andP => H1 H2.
rewrite -IH // /add_seq.
have X : a \in unzip1 (cons (n, w) tl) = false.
  apply/negbTE.
  rewrite /unzip1 /= in_cons negb_or X.ltA_total H1.
  move/(@mem_ub _ _ X.ltA_irr) : H2 => ->.
  by rewrite orbC.
rewrite X.
have XX : a \in unzip1 tl = false.
  rewrite /dom /= in_cons in X.
  move/negbT : X.
  rewrite negb_or.
  case/andP => H3.
  by move/negbTE.
rewrite XX /=.
case: ifP => Y.
- move: (X.ltA_trans Y H1).
  by rewrite X.ltA_irr.
- case: ifP => [/eqP Z | Z //].
  subst.
  by rewrite X.ltA_irr in H1.
Qed.

Lemma in_add_seq k a b : (a, b) \in add_seq a b k.
Proof.
rewrite /add_seq.
case: ifPn => X.
- by apply in_unzip1_in_upd_seq.
- rewrite mem_add_map //; exact/negP.
Qed.

Lemma in_map_add_seq {A : eqType} (f : l * v -> A) k a b : f (a, b) \in map f (add_seq a b k).
Proof.
move: (in_add_seq k a b) => H. rewrite /dom. apply/mapP. by exists (a, b).
Qed.

Lemma in_unzip1_add_seq_remains k x a b : x \in unzip1 k -> x \in unzip1 (add_seq a b k).
Proof.
move=> H.
rewrite /add_seq.
case: ifP => X.
- by rewrite unzip1_upd_seq.
- apply in_unzip1_add_map; try ord_pro||auto.
Qed.

Lemma in_add_seq_remains : forall k x a b, x \in k -> ~ a \in unzip1 k -> x \in add_seq a b k.
Proof.
elim => //; case=> [hd1 hd2] /= tl IH [x1 x2] /= a b.
rewrite !in_cons; case/orP.
- case/andP=> /= /eqP => X; subst. move/eqP => X; subst. move/negP. case/norP => X Y.
  rewrite /add_seq.
  have -> : a \in unzip1 ((hd1, hd2) :: tl) = false.
    by rewrite /= in_cons (negbTE Y) (negbTE X).
  rewrite /= (negbTE X) /=.
  case: ifP => U.
  + by rewrite /= !in_cons eq_refl /= orbC.
  + by rewrite /= !in_cons eq_refl.
- move=> X /negP /norP[Y Z].
  rewrite eq_sym in Y.
  rewrite /add_seq /= !in_cons eq_sym (negbTE Y) /= (negbTE Z) /=.
  case: ifP => V.
  + by rewrite /= !in_cons X 2!orbT.
  + rewrite /=.
    move/negP in Z.
    move: (IH (x1,x2) a b X Z).
    move/negP in Z.
    rewrite /add_seq (negbTE Z) /= in_cons => ->.
    by rewrite orbT.
Qed.

Lemma in_add_seq_inv : forall k x a b, x \in add_seq a b k -> x = (a, b) \/ x \in k.
Proof.
elim=> [[h1 h2] /= tl b | [h1 h2] /= tl IH [x1 x2] y w H].
- rewrite /add_seq /= in_cons orbC /=; by move/eqP; left.
- rewrite /add_seq /= in H.
  case/boolP: (h1 == y); [move/eqP => X; subst | move/negbTE => X].
  + move: H.
    rewrite in_cons eq_refl /= in_cons.
    case/orP => H.
    * by left; apply/eqP.
    * right; by rewrite in_cons H orbC.
  + rewrite !in_cons eq_sym X /= in H.
    case: ifP H => Y.
    * rewrite /=.
      case/orP => H.
      - right; by rewrite in_cons H.
      - move: (IH (x1,x2) y w).
        rewrite /add_seq Y.
        case/(_ H) => {}H.
        + by left.
        + right; by rewrite in_cons H orbC.
    * move=> H.
      case: ifP H => Z.
      - rewrite in_cons; case/orP => H.
        + left; by apply/eqP.
        + by right.
      - rewrite in_cons. case/orP => H.
        + right; by rewrite in_cons H.
        + move: (IH (x1,x2) y w).
          rewrite /add_seq Y.
          case/(_ H) => {}H.
          * by left.
          * right; by rewrite in_cons H orbC.
Qed.

Lemma in_map_add_seq_inv {A : eqType} f k (x : A) a b :
  x \in map f (add_seq a b k) -> x = f (a, b) \/ x \in map f k.
Proof.
case/mapP => x1.
case/in_add_seq_inv; [move=> ? ?; subst x1 x | move=> Hx1 ?; subst x].
- by left.
- right. apply/mapP; by exists x1.
Qed.

Lemma get_seq_add_seq_eq k n w : get_seq n (add_seq n w k) = Some w.
Proof.
rewrite /add_seq.
case: ifP => X.
- by rewrite /= /get_seq ocamlfind_upd_seq.
- rewrite /get_seq ocamlfind_add_map //=; by apply/negP/negbT.
Qed.

Lemma get_add_eq k n w : get n (add n w k) = Some w.
Proof. rewrite /get /add /=; by apply get_seq_add_seq_eq. Qed.

Lemma get_seq_add_seq_neq k n w n' : n != n' -> get_seq n' (add_seq n w k) = get_seq n' k.
Proof.
move=> Hnn'.
rewrite {1}/get_seq /add_seq.
case: ifPn => X.
- rewrite /= ocamlfind_upd_seq' //; by apply/eqP.
- rewrite ocamlfind_add_map' => //; [by apply/eqP | by apply/negP].
Qed.

Lemma get_add_neq k n w n' : n != n' -> get n' (add n w k) = get n' k.
Proof. rewrite /get /add /=; by apply get_seq_add_seq_neq. Qed.

Lemma in_dom_add: forall k n n' w, n \in dom (add n' w k) = (n == n') || (n \in dom k).
Proof.
case=> k Hk n n' w; rewrite /add /dom /= /add_seq.
case: ifP => H1.
- rewrite unzip1_upd_seq.
  apply/idP/idP.
  + move=> ->; by rewrite orbC.
  + case/orP => //.
    by move/eqP => ->.
- apply/idP/idP.
  + move=> H.
    apply/orP.
    apply in_add_app_inv_unzip1 in H.
    case: H => H; try auto.
    by left; apply/eqP.
  + case/orP => H.
    * move/eqP in H; subst n'.
      apply in_unzip1_add_map'; by ord_pro.
    * apply in_unzip1_add_map => //; by ord_pro.
Qed.

Lemma add_eq_in_dom : forall k n w, n \in dom (add n w k).
Proof.
case=> h Hk n w.
rewrite /add /= /dom /=.
move: (in_add_seq h n w) => H.
apply/mapP.
by exists (n, w).
Qed.

Lemma add_neq_notin_dom: forall k n n' w, n != n' -> n \in dom (add n' w k) -> n \in dom k.
Proof.
case=> k Hk n n' w nn'.
rewrite /dom /add /=.
case/mapP.
case=> x1 x2 /=.
case/in_add_seq_inv.
case=> ? ? ?; subst; by rewrite eqxx in nn'.
move=> H ?; subst x1.
apply/mapP; by exists (n, x2).
Qed.

Lemma upd_seq_add_map : forall k n w w', n \in unzip1 k = false ->
  upd_seq n w (add_map X.ltA n w' k) = add_map X.ltA n w k.
Proof.
elim=> //=.
- move=> n w w'; by rewrite eq_refl.
- move=> [a b] /= tl IH n w w'.
  rewrite !in_cons; move/norP => [H1 H2].
  rewrite X.ltA_total in H1.
  case/orP:H1 => H1.
  rewrite H1 /= eq_refl //.
  rewrite (flip X.ltA_trans X.ltA_irr H1) /= eq_sym (lt_neq X.ltA_total H1) /=
    eq_sym (lt_neq X.ltA_total H1) /= IH //=.
  apply/negP.
  by apply/negP.
Qed.

Lemma add_map_upd_seq : forall k n' w' n w, n' <> n -> n' \in unzip1 k -> n \in unzip1 k = false ->
  add_map X.ltA n w (upd_seq n' w' k) = upd_seq n' w' (add_map X.ltA n w k).
Proof.
elim=> //; case=> [a b] /= tl IH n' w' n w.
move/eqP => H.
rewrite !in_cons; case/orP => X.
- move/eqP : X => X; subst.
  case/norP => _ H2.
  rewrite eq_sym in H.
  rewrite eq_refl /= (negbTE H) /=.
  move: H.
  rewrite X.ltA_total. case/orP => X.
  + by rewrite X /= eq_sym (lt_neq X.ltA_total X) /= eq_refl.
  + by rewrite (flip X.ltA_trans X.ltA_irr X) /= eq_refl.
- case/norP => H1 H2.
  + case: ifP => Y.
    move: H1. rewrite X.ltA_total. case/orP => H1.
    * rewrite H1 /= (lt_neq X.ltA_total H1) /= H1 //.
      by rewrite (negbTE H) Y.
    * rewrite (flip X.ltA_trans X.ltA_irr H1) (eq_sym n a) (lt_neq X.ltA_total H1) /= Y.
      by rewrite (flip X.ltA_trans X.ltA_irr H1) eq_sym (lt_neq X.ltA_total H1).
  + rewrite /= (negbTE H1).
    move: H1. rewrite X.ltA_total. case/orP => H1.
    * by rewrite H1 /= (negbTE H) /= Y.
    * rewrite (flip X.ltA_trans X.ltA_irr H1) /= Y /= IH //.
      by apply/eqP.
      by destruct (n \in unzip1 tl).
Qed.

Lemma add_seq_add_seq_eq k n w' w : add_seq n w (add_seq n w' k) = add_seq n w k.
Proof.
rewrite /add_seq /=.
case/boolP : (n \in unzip1 k) => X.
- by rewrite unzip1_upd_seq X upd_seq_upd_seq_eq.
- rewrite /= in_unzip1_add_map'; try ord_pro.
  rewrite upd_seq_add_map //; by apply/negbTE.
Qed.

Lemma add_seq_add_seq_neq k n' w' n w : n' <> n ->
  add_seq n w (add_seq n' w' k) = add_seq n' w' (add_seq n w k).
Proof.
move=> Hn'n.
rewrite /add_seq /=.
case/boolP : (n' \in unzip1 k) => X.
- rewrite /= unzip1_upd_seq.
  case: ifP => Y.
  + rewrite /= unzip1_upd_seq X //.
    apply upd_seq_upd_seq_neq; by auto.
  + rewrite /= in_unzip1_add_map //; try ord_pro||auto.
    by apply add_map_upd_seq.
- rewrite /=.
  case/boolP : (n \in unzip1 k) => Y.
  + rewrite /= unzip1_upd_seq (negbTE X) /= in_unzip1_add_map; try ord_pro||auto.
    symmetry; apply add_map_upd_seq; auto.
    by apply/negbTE.
  + rewrite /=.
    set c0 := {1}(_ \in unzip1 (add_map _ _ _ _)).
    set c1 := {1}(_ \in unzip1 (add_map _ _ _ _)).
    have : c0 = false.
      apply/negP.
      rewrite /c0.
      apply: notin_unzip1_add_map; try ord_pro||auto.
      by rewrite (negbTE Y).
      by rewrite (negbTE X).
    have : c1 = false.
      apply/negP.
      rewrite /c1.
      apply: notin_unzip1_add_map; try ord_pro||auto.
      by rewrite (negbTE X).
      by rewrite (negbTE Y).
    move=> -> ->.
    apply add_map_comm; try ord_pro.
    by auto.
Qed.

Lemma upd_seq_is_add_seq : forall k n w, n \in unzip1 k -> upd_seq n w k = add_seq n w k.
Proof.
elim=> //=.
move=> [h1 h2] /= tl IH n w.
rewrite !in_cons; case/orP => X.
move/eqP in X; subst h1.
rewrite eq_refl /= /add_seq /= eq_refl //= !in_cons eq_refl //=.
case: ifP => Y.
- rewrite /add_seq /=.
  by rewrite Y //= !in_cons Y.
- by rewrite /= /add_seq /= !in_cons /= Y X.
Qed.

Lemma upd_seq_add_seq : forall k n w w', upd_seq n w (add_seq n w' k) = add_seq n w k.
Proof.
elim=> //=.
- move=> n w w'.
  by rewrite eq_refl.
- move=> [a b] /= k IH n w w'.
  rewrite /add_seq /= !in_cons.
  case/boolP : (n == a) => X.
  + by move/eqP in X; subst n; rewrite /= eqxx.
  + rewrite /=.
    case: ifP => Y.
    * by rewrite /= (negbTE X) /= upd_seq_upd_seq_eq.
    * case: ifP => Z.
      - by rewrite /= eqxx.
      - rewrite /= (negbTE X) /=; congr cons.
        move: (IH n w w').
        by rewrite /add_seq Y.
Qed.

Lemma add_seq_upd_seq : forall k a b, add_seq a b (upd_seq a b k) = add_seq a b k.
Proof.
elim=> //.
case=> [a' b'] tl IH a b.
case/boolP : (a == a') => X.
  move/eqP in X; subst a'.
  by rewrite /= eqxx /add_seq /= in_cons eqxx.
rewrite /= (negbTE X) /add_seq /= !in_cons (negbTE X) /= unzip1_upd_seq_invariant.
case: ifP => Y.
  by rewrite /= upd_seq_upd_seq_eq.
rewrite upd_seq_invariant //; by move/negP : Y.
Qed.

Lemma upd_seq_add_seq_neq: forall k n n' w w', n' <> n ->
  upd_seq n w (add_seq n' w' k) = add_seq n' w' (upd_seq n w k).
Proof.
elim=> //=.
- move=> n n' w w' H.
  suff : n == n' = false by move=> ->.
  by apply/eqP; auto.
- move=> [a b] /= k IH n n' w w' Hnn'.
  case: ifP => X.
  + move/eqP in X; subst.
    rewrite /add_seq.
    case/boolP : (n' \in unzip1 k) => Y.
    * rewrite /=.
      rewrite !in_cons Y orbC /=.
      have Z : n' == a = false by apply/eqP; auto.
      by rewrite Z /= eq_refl.
    * rewrite /=.
      have Z : a == n' = false by apply/eqP; auto.
      rewrite !in_cons eq_sym Z /= (negbTE Y) /= .
      move/eqP in Hnn'.
      rewrite X.ltA_total in Hnn'.
      case/orP:Hnn'=>X.
      rewrite X /= Z eq_refl //=.
      by rewrite (flip X.ltA_trans X.ltA_irr X) /= eq_refl.
  + rewrite /add_seq /=.
    rewrite unzip1_upd_seq.
    case/boolP : (n' \in unzip1 k) => Y.
    * rewrite !in_cons Y orbC /=.
      case: ifP => Z.
      - move/eqP in Z; subst.
        by rewrite /= X.
      - rewrite /= X /=.
        case/boolP : (n \in unzip1 k) => W.
          by rewrite upd_seq_upd_seq_neq; auto.
        move/negP in W.
        rewrite (upd_seq_invariant _ _ W) //.
        have U : ~ n \in unzip1 (upd_seq n' w' k) by rewrite unzip1_upd_seq.
        by rewrite (upd_seq_invariant _ _ U).
    * case/boolP : (a == n') => Z.
      - move/eqP in Z; subst.
        by rewrite !in_cons eq_refl /= X.
      - move/negbTE : Z => Z.
        rewrite !in_cons eq_sym Z /= (negbTE Y) /=.
        move/negP: Z.
        move/negP.
        rewrite X.ltA_total.
        case/orP => Z.
        + rewrite (flip X.ltA_trans X.ltA_irr Z) /= X /=.
          case/boolP : (n \in unzip1 k) => W.
          rewrite -add_map_upd_seq; auto.
          by apply/negbTE.
          rewrite upd_seq_invariant; last first.
            rewrite /dom.
            apply: notin_unzip1_add_map; try ord_pro||auto.
            move/eqP; by rewrite (negbTE W).
            move/eqP; by rewrite (negbTE Y).
          rewrite upd_seq_invariant //; by apply/negP.
        + rewrite Z /=.
          have -> : n == n' = false by apply/eqP; auto.
          by rewrite X.
Qed.

Fixpoint app_seq (h1 h2 : seq (l * v)) :=
  match h1 with
    | [::] => h2
    | (h, h') :: tl => add_seq h h' (app_seq tl h2)
  end.

Lemma lb_unzip1_app_seq : forall l1 l2 x,
  lb X.ltA x (unzip1 l1) -> lb X.ltA x (unzip1 l2) ->
  lb X.ltA x (unzip1 (app_seq l1 l2)).
Proof.
elim=> //.
case=> h1 h1' t1 IH l2 x /=.
case/andP => H1 H1' H2.
rewrite /add_seq.
case: ifP => X.
- by rewrite unzip1_upd_seq_invariant IH.
- apply (lb_unzip1_add_map _ _ X.ltA_trans X.ltA_total X.ltA_irr) => //.
  by apply IH.
Qed.

Lemma ordered_app_seq : forall h1 h2,
  ordered X.ltA (unzip1 h1) -> ordered X.ltA (unzip1 h2) ->
  ordered X.ltA (unzip1 (app_seq h1 h2)).
Proof.
elim => //=.
move=> [la va] /= l0 H h2.
case/ordered_inv => H1 H2 H3.
by apply ordered_add_seq, H.
Qed.

Definition union h1 h2 := mk_t _ (ordered_app_seq _ _ (prf h1) (prf h2)).
Local Notation "k '\U' m" := (union k m).

Lemma app_seq_nil : forall k, ordered X.ltA (unzip1 k) -> app_seq k [::] = k.
Proof.
elim => //=.
move=> [la va] /= l0 IH.
case/ordered_inv => H1 H2.
by rewrite IH // add_seq_is_cons.
Qed.

Lemma unionhe h : h \U emp = h.
Proof. apply extensionality => x. rewrite /get /= app_seq_nil //. by case: h. Qed.

Lemma unioneh h : emp \U h = h.
Proof. apply extensionality => x. rewrite /get /=. by case: h. Qed.

Lemma app_seq_com : forall l1 l2, ordered X.ltA (unzip1 l1) -> ordered X.ltA (unzip1 l2) ->
  dis (unzip1 l1) (unzip1 l2) -> app_seq l1 l2 = app_seq l2 l1.
Proof.
elim=> [* | [a b] /= l0 Hl0].
- by rewrite app_seq_nil.
- elim.
  + move/ordered_inv => [H1 H2] _ _.
    by rewrite app_seq_nil // add_seq_is_cons.
  + move=> [a0 b0] /= l1 Hl1.
    case/ordered_inv => H1 H2.
    case/ordered_inv => H3 H4 H.
    rewrite -Hl1 //; last 2 first.
      by constructor.
      case: ifP H => //.
      move/negbT. rewrite in_cons negb_or. case/andP=> a_a0 a_l1 H.
      rewrite (negbTE a_l1).
      move/disP : H => /seq_ext.disj_sym /=.
      by case/(@disj_cons_inv X.A) => /seq_ext.disj_sym/disP.
    rewrite -add_seq_add_seq_neq; last first.
      move=> X; subst; by rewrite in_cons eqxx /= in H.
    rewrite Hl0 => //; last 2 first.
      by constructor.
      by case: ifP H.
    rewrite Hl0 //=.
    move: H.
    case: ifP => //.
    move/negbT. rewrite in_cons negb_or. case/andP=> a_a0 a_l1 H.
    move/disP : H => /seq_ext.disj_sym /=.
    by case/(@disj_cons_inv X.A) => /seq_ext.disj_sym/disP.
Qed.

Lemma unionC : forall h1 h2, h1 # h2 -> h1 \U h2 = h2 \U h1.
Proof.
move=> [h1 H1] [h2 H2] H.
apply equal_eq.
rewrite /union /equal /=; by apply app_seq_com.
Qed.

Lemma in_unzip1_app_seq : forall l1 l2 n, n \in unzip1 l1 \/ n \in unzip1 l2 -> n \in unzip1 (app_seq l1 l2).
Proof.
elim=> //=.
- move=> l2 n [X|X] //; auto.
- move=> [h1 h2] /= tl IH l2 n.
  case.
  + rewrite in_cons; case/orP.
    * move/eqP => X; subst.
      by apply in_map_add_seq.
    * move=> X.
      apply in_unzip1_add_seq_remains.
      by apply IH; left.
  + move=> X.
    apply in_unzip1_add_seq_remains.
    by apply IH; right.
Qed.

Lemma in_dom_union_L : forall x h1 h2, x \in dom h1 -> x \in dom (h1 \U h2).
Proof.
move=> x [h1 Hh1] [h2 Hh2] /= x_in_h1.
rewrite /dom /= in_unzip1_app_seq //; by left.
Qed.

Lemma in_map_app_seq_inv {A : eqType} (f : l * v -> A) : forall l1 l2 n,
  n \in map f (app_seq l1 l2) -> n \in map f l1 \/ n \in map f l2.
Proof.
elim=> [/= * | [x1 x2] /= l1 IH l2 n].
- by right.
- case/in_map_add_seq_inv; [move=> H; subst n | ].
  + rewrite in_cons eqxx; by left.
  + case/IH => H.
    * rewrite in_cons H orbC /=; by left.
    * by right.
Qed.

Lemma in_cdom_union_inv : forall t a b, t \in cdom (a \U b) -> t \in cdom a \/ t \in cdom b.
Proof. move=> x [a Ha] [b Hb]. rewrite /cdom /=. case/in_map_app_seq_inv; tauto. Qed.

Lemma in_dom_union_inv : forall t a b, t \in dom (a \U b) -> t \in dom a \/ t \in dom b.
Proof. move=> x [a Ha] [b Hb]. rewrite /dom /=. case/in_map_app_seq_inv; tauto. Qed.

Lemma notin_unzip1_app_seq l1 l2 x :
  ~ x \in unzip1 l1  -> ~ x \in unzip1 l2 -> ~ x \in (unzip1 (app_seq l1 l2)).
Proof. move=> Hl1 Hl2. case/in_map_app_seq_inv => H; tauto. Qed.

Lemma in_app_seq : forall l1 l2 n, ordered X.ltA (unzip1 l1) ->
  dis (unzip1 l1) (unzip1 l2) -> n \in l1 -> n \in app_seq l1 l2.
Proof.
elim=> //=.
move=> [hd1 hd2] /= tl IH l2 [n1 n2] /=.
move/ordered_inv => [H1 H2] H3 /=.
rewrite in_cons.
case/orP.
- case/eqP=> X Y; subst.
  by apply in_add_seq.
- move=> X.
  apply in_add_seq_remains.
  * apply IH => //.
    move: H3.
    by case: ifP.
  * apply notin_unzip1_app_seq.
    - move/(mem_lb X.ltA_irr) : H2.
      by move/negP.
    - move: H3.
      by case: ifP.
Qed.

Lemma in_app_seq_inv : forall l1 l2 n, ordered X.ltA (unzip1 l1) ->
  dis (unzip1 l1) (unzip1 l2) -> n \in app_seq l1 l2 -> n \in l1 \/ n \in l2.
Proof.
elim=> //=.
- move=> l2 n _ _ X; auto.
- move=> [hd1 hd2] /= tl IH l2 [n1 n2] /=.
  move/ordered_inv => [H1 H2] H3 /= H.
  apply in_add_seq_inv in H.
  rewrite !in_cons.
  case:H.
  + move=> ->; rewrite eqxx; by left.
  + move=> H.
    move: H3.
    case: ifP => // hd1_l2 tl_l2.
    case: (IH l2 (n1, n2) H1) => //.
    * move=> ->; rewrite orbC /=; by left.
    * move=> ->; by right.
Qed.

Lemma upd_seq_app_seq : forall l1 l2 n z, n \in unzip1 l1 ->
  app_seq (upd_seq n z l1) l2 = upd_seq n z (app_seq l1 l2).
Proof.
elim=> //.
move=> [a b] /= tl IH l2 n z.
rewrite in_cons.
case/orP.
- move/eqP => X ; subst.
  by rewrite eq_refl /= upd_seq_add_seq.
- move=> X.
  case: ifP => Z.
  - move/eqP in Z; subst.
    by rewrite /= upd_seq_add_seq.
  - rewrite /= IH // upd_seq_add_seq_neq //.
    by move/eqP : Z; auto.
Qed.

Lemma add_seq_app_seq: forall l1 l2 n w,
  add_seq n w (app_seq l1 l2) = app_seq (add_seq n w l1) l2.
Proof.
elim=> //=.
move=> [h1 h2] /= tl IH l2 n w.
rewrite {3}/add_seq /=.
case/boolP : (h1 == n) => Y.
- move/eqP in Y; subst.
  by rewrite !in_cons eq_refl /= add_seq_add_seq_eq.
- move/negbTE : Y => Y.
  rewrite !in_cons eq_sym Y /=.
  case: ifP => U.
  + rewrite /= upd_seq_app_seq // -upd_seq_add_seq_neq; last by move/eqP; rewrite Y.
    rewrite upd_seq_is_add_seq // in_unzip1_add_seq_remains // in_unzip1_app_seq //; by left.
  + case: ifP => Z //.
    rewrite add_seq_add_seq_neq; last by move/eqP: Y.
    by rewrite IH {2}/add_seq U.
Qed.

Lemma add_seq_app_seq2 : forall l1 l2 n w, n \notin unzip1 l1 ->
  add_seq n w (app_seq l1 l2) = app_seq l1 (add_seq n w l2).
Proof.
elim=> //=.
move=> [h1 h2] /= tl IH l2 n w.
rewrite in_cons negb_or.
case/andP => H1 H2.
rewrite add_seq_add_seq_neq; last by move/eqP : H1; auto.
by rewrite IH.
Qed.

Lemma app_seq_upd_seq_upd_seq : forall l1 l2 a b,
  app_seq (upd_seq a b l1) (upd_seq a b l2) = upd_seq a b (app_seq l1 l2).
Proof.
elim=> //; case=> h1 h2 t1 IH l2 a b /=.
case: ifP => X.
- move/eqP in X; subst h1.
  rewrite /= upd_seq_add_seq add_seq_app_seq.
  case/boolP : (a \in unzip1 t1) => Y.
  + rewrite -upd_seq_is_add_seq // IH -upd_seq_is_add_seq // in_unzip1_app_seq //; by left.
  + rewrite -add_seq_app_seq.
    move/negP in Y.
    by rewrite -{1}(upd_seq_invariant t1 _ Y b) IH add_seq_upd_seq.
- rewrite /= IH upd_seq_add_seq_neq //; move/eqP : X; by auto.
Qed.

Lemma app_seq_add_seq_add_seq : forall l1 l2 a b,
  app_seq (add_seq a b l1) (add_seq a b l2) = add_seq a b (app_seq l1 l2).
Proof.
elim=> [l2 a b | [h1 h2] t1 IH l2 a b /=].
- by rewrite /= add_seq_add_seq_eq.
- rewrite {1}/add_seq /= !in_cons.
  case/boolP : (a == h1) => X.
  + move/eqP : X => X; subst h1; rewrite /=.
    by rewrite add_seq_add_seq_eq add_seq_app_seq IH.
  + rewrite /=.
    case: ifP => Y.
    * move: (IH l2 a b).
      rewrite {1}/add_seq Y /=.
      move=> ->.
      rewrite add_seq_add_seq_neq //.
      by move/eqP : X.
    * case: ifP => Z.
      - rewrite /= add_seq_add_seq_neq; last by move/eqP : X; auto.
        rewrite add_seq_app_seq IH add_seq_add_seq_neq //.
        by move/eqP : X.
      - rewrite /= add_seq_add_seq_neq; last by move/eqP : X; auto.
        by rewrite -IH {4}/add_seq Y.
Qed.

Lemma unionA : forall h1 h2 h3, h1 \U (h2 \U h3) = (h1 \U h2) \U h3.
Proof.
move=> [h1 H1] [h2 H2] [h3 H3].
apply equal_eq.
rewrite /equal /union /=.
move: h1 H1.
elim=> //=.
move=> [a b] /= l1 IH.
move/ordered_inv => [X Y].
by rewrite IH // add_seq_app_seq.
Qed.

Lemma get_seq_app_seq_L : forall l1 l2 n z,
  get_seq n l1 = Some z -> get_seq n (app_seq l1 l2) = Some z.
Proof.
elim=> [|[a b] l1 IH] //= l2 n z.
case/boolP: (n == a).
- move/eqP => X; subst n.
  rewrite get_seq_cons.
  case=> X; subst b.
  by rewrite get_seq_add_seq_eq.
- move=> X.
  rewrite get_seq_cons' => Y; last by move/eqP: X; auto.
  rewrite get_seq_add_seq_neq; last by rewrite eq_sym.
  by apply IH.
Qed.

Lemma get_seq_app_seq_R l1 l2 n z :
  ordered X.ltA (unzip1 l1) -> ordered X.ltA (unzip1 l2) -> dis (unzip1 l1) (unzip1 l2) ->
  get_seq n l2 = Some z -> get_seq n (app_seq l1 l2) = Some z.
Proof. move=> H1 H2 H H'. rewrite app_seq_com //. by apply get_seq_app_seq_L. Qed.

Lemma get_union_sing_eq x z st : get x (sing x z \U st) = Some z.
Proof. by rewrite /get /sing /= get_seq_add_seq_eq. Qed.

Lemma get_union_sing_neq x y z st : x <> y -> get x (sing y z \U st) = get x st.
Proof. move=> Hxy. rewrite /get /sing /= get_seq_add_seq_neq // eq_sym; exact/eqP. Qed.

Lemma get_union_Some_inv : forall h1 h2 n z,
  get n (h1 \U h2) = Some z -> get n h1 = Some z \/ get n h2 = Some z.
Proof.
move=> [h1 H1] [h2 H2].
rewrite /union /get /=.
move: h1 H1 h2 H2.
elim=> //=.
- by auto.
- move=> [a b] /= l0 IH.
  move/ordered_inv => [H1 H2] h2 Hh2 n z H3.
  case/boolP : (a == n) => X.
  + move/eqP:X => X; subst.
    rewrite get_seq_add_seq_eq in H3.
    case:H3 => H3; subst.
    rewrite /get_seq /= eq_refl //=.
    by auto.
  + rewrite get_seq_add_seq_neq // in H3.
    rewrite get_seq_cons'; last by move/eqP: X; auto.
    by apply IH.
Qed.

Lemma get_union_L : forall h1 h2, h1 # h2 ->
  forall n z, get n h1 = Some z -> get n (h1 \U h2) = Some z.
Proof.
move=> [h1 H1] [h2 H2] /= H n z.
rewrite /get /= => H'.
by apply get_seq_app_seq_L.
Qed.

Lemma get_union_R : forall h1 h2, h1 # h2 ->
  forall n z, get n h2 = Some z -> get n (h1 \U h2) = Some z.
Proof.
move=> [h1 H1] [h2 H2] /= H n z.
rewrite /get /= => H'.
by apply get_seq_app_seq_R.
Qed.

Lemma get_union_None_inv : forall h1 h2 n,
  get n (h1 \U h2) = None -> get n h1 = None /\ get n h2 = None.
Proof.
move=> [h1 Hh1] [h2 Hh2] n.
rewrite /get /= => H.
move/get_seq_None_notin : H => H.
split.
apply notin_get_seq_None.
contradict H.
rewrite in_unzip1_app_seq //; by left.
apply notin_get_seq_None.
contradict H.
rewrite in_unzip1_app_seq //; by right.
Qed.

Lemma upd_union_L : forall h1 h2, h1 # h2 -> forall n z z1, get n h1 = Some z1 ->
  upd n z (h1 \U h2) = upd n z h1 \U h2.
Proof.
move=> [h1 H1] [h2 H2] /= Hdis n z z1 H'.
apply equal_eq.
rewrite /get /upd /equal /= upd_seq_app_seq //.
rewrite /get /= in H'.
by apply get_seq_Some_in_unzip1 in H'.
Qed.

Lemma upd_union_R : forall h1 h2, h1 # h2 -> forall n z z2, get n h2 = Some z2 ->
  upd n z (h1 \U h2) = h1 \U upd n z h2.
Proof.
move=> [h1 H1] [h2 H2] /= Hdis n z z2 H'.
apply equal_eq.
rewrite /get /upd /equal /= app_seq_com //.
rewrite -upd_seq_app_seq //; last first.
  rewrite /get /= in H'.
  by apply get_seq_Some_in_unzip1 in H'.
rewrite app_seq_com //; last first.
  rewrite unzip1_upd_seq.
  by apply/disP/seq_ext.disj_sym/disP.
by rewrite unzip1_upd_seq.
Qed.

Lemma elts_union_sing : forall h n w, lb ltl n (dom h) ->
  elts (sing n w \U h) = (n, w) :: elts h.
Proof.
move=> [k Hk] /= n w Hdisj; rewrite (add_seq_is_cons k n w) //; by apply lt_lb.
Qed.

Lemma dom_union_sing h n w : lb ltl n (dom h) ->
  dom (sing n w \U h) = n :: dom h.
Proof. move=> H; by rewrite -elts_dom elts_union_sing. Qed.

Lemma cdom_union_sing k (a : l) b : lb ltl a (dom k) ->
  cdom (sing a b \U k) = b :: cdom k.
Proof. move=> H; by rewrite -elts_cdom elts_union_sing. Qed.

Lemma cdom_union : forall h1 h2,
  (forall i j, i \in dom h1 -> j \in dom h2 -> ltl i j) ->
  cdom (h1 \U h2) = cdom h1 ++ cdom h2.
Proof.
case.
elim=> //; case=> h11 h12 t1 IH H_h1_t1 [h2 H2].
rewrite /dom /cdom /= => i_j.
rewrite /unzip1 /= in H_h1_t1.
case/ordered_inv : H_h1_t1 => H_t1 H_h11_t1.
move: {IH}(IH H_t1 (mk_t _ H2)) => IH.
rewrite /cdom /= in IH.
rewrite add_seq_is_cons /=; last first.
  apply lb_unzip1_app_seq; first by [].
  apply lt_lb => n Hn.
  apply i_j; last by [].
  by rewrite in_cons eqxx.
rewrite IH // => i j.
rewrite /dom /= => Hi Hj.
apply i_j => //.
by rewrite in_cons Hi orbC.
Qed.

Lemma dom_union : forall h1 h2,
  (forall i j, i \in dom h1 -> j \in dom h2 -> X.ltA i j) ->
  dom (h1 \U h2) = dom h1 ++ dom h2.
Proof.
case.
elim=> //; case=> h11 h12 t1 IH H_h1_t1 [h2 H2].
rewrite /dom /cdom /= /= => i_j.
rewrite /unzip1 /= in H_h1_t1.
case/ordered_inv : H_h1_t1 => H_t1 H_h11_t1.
move: {IH}(IH H_t1 (mk_t _ H2)) => IH.
rewrite /dom /= in IH.
rewrite add_seq_is_cons /=.
- rewrite IH // => i j.
  rewrite /dom /= => Hi Hj.
  apply i_j.
  by rewrite in_cons Hi orbC.
  exact Hj.
- apply lb_unzip1_app_seq; first by [].
  apply lt_lb => n Hn.
  apply i_j; last by [].
  by rewrite in_cons eqxx.
Qed.

Lemma sing_union_sing : forall x v1 v2, sing x v1 \U sing x v2 = sing x v1.
Proof.
move=> x v1 v2.
rewrite /sing /union /=.
apply mk_t_pi => /=.
by rewrite /add_seq /= mem_seq1 eqxx.
Qed.

Lemma add_seq_Permutation : forall l a b, a \notin unzip1 l ->
  Permutation (add_seq a b l) ((a, b) :: l).
Proof.
elim.
- move=> a b /= _; by apply Permutation_refl.
- move=> [hd1 hd2] tl IH a b /=.
  rewrite in_cons negb_or.
  case/andP => H1 H2.
  rewrite /add_seq.
  have -> : a \in unzip1 (cons (hd1, hd2) tl) = false.
    by rewrite /unzip1 /= in_cons /= (negbTE H1) /= (negbTE H2).
  rewrite /= (negbTE H1).
  rewrite X.ltA_total in H1.
  case/orP : H1 => H1.
  rewrite H1 /=.
  by apply Permutation_refl.
  rewrite (flip X.ltA_trans X.ltA_irr) //=.
  eapply Permutation_trans; last by apply perm_swap.
  apply perm_skip.
  move/negbTE : (H2) => H2'.
  move/(IH _ b) : H2.
  by rewrite /add_seq H2'.
Qed.

Lemma app_seq_Permutation : forall k l, ordered X.ltA (unzip1 k) ->
  dis (unzip1 k) (unzip1 l) -> Permutation (app_seq k l) (k ++ l).
Proof.
elim.
- move=> k /= _ _; by apply Permutation_refl.
- move=> [hd1 hd2] tl IH m Hord Hdis /=.
  rewrite /= in Hord.
  case/ordered_inv : Hord => Hord1 Hord2.
  rewrite /unzip1 /= in Hdis.
  move: Hdis.
  case: ifP => //.
  move=> hd1_m tl_m.
  eapply Permutation_trans.
  + apply add_seq_Permutation.
    apply/negP.
    apply notin_unzip1_app_seq.
    apply/negP.
    by apply (mem_lb X.ltA_irr).
    by rewrite hd1_m.
  + by apply perm_skip, IH.
Qed.

Lemma Permutation_dom_union : forall h1 h2, h1 # h2 ->
  Permutation (dom (h1 \U h2)) (dom h1 ++ dom h2).
Proof.
case=> [h1 H1] [h2 H2].
rewrite /disj /= => Hdis.
rewrite /dom /unzip1 -map_cat.
apply Permutation_map => /=.
by apply app_seq_Permutation.
Qed.

Lemma app_seq_reg : forall h0 h0' h1 h2,
  ordered X.ltA (unzip1 h0) -> unzip1 h0 = unzip1 h0' ->
  ordered X.ltA (unzip1 h1) -> ordered X.ltA (unzip1 h2) ->
  app_seq h0 h1 = app_seq h0' h2 ->
  dis (unzip1 h1) (unzip1 h0) -> dis (unzip1 h2) (unzip1 h0') ->
  h0 = h0' /\ h1 = h2.
Proof.
elim=> //; first by case.
move=> [hd1 hd2] /= tl IH.
case=> //.
case=> hd1' hd2' tl' l1 l2.
move/ordered_inv => [Hhd1 Htl] H00' Hl1 Hl2 H Hl1' Hl2'.
rewrite /= in H00'.
case : H00' => X Y; subst hd1'.
rewrite /add_seq in H.
have H1 : hd1 \in unzip1 (app_seq tl l1) = false.
  apply/negP.
  apply notin_unzip1_app_seq.
  apply mem_lb in Htl; try ord_pro.
  by rewrite (negbTE Htl).
  move/disP : Hl1' => /seq_ext.disj_sym /disP /=.
  by case: ifP.
rewrite H1 in H.
have H2 : hd1 \in (unzip1 (app_seq tl' l2)) = false.
  apply/negP.
  apply notin_unzip1_app_seq.
  apply mem_lb in Htl; try ord_pro.
  by rewrite -Y (negbTE Htl).
  move/disP : Hl2' => /seq_ext.disj_sym /disP /=.
  by case: ifP.
rewrite /= /add_seq in H.
rewrite H2 in H.
apply add_map_reg in H; try ord_pro.
case: H => H3 H4.
subst hd2'.
- move: {IH}(IH tl' l1 l2 Hhd1 Y Hl1 Hl2 H4) => IH.
  rewrite dis_sym /= in Hl2'.
  move: Hl2'.
  case: ifP => // hd1_l2 tl'_l2.
  rewrite dis_sym /= in Hl1'.
  move: Hl1'.
  case: ifP => // hd1_l1 tl_l1.
  rewrite dis_sym in tl'_l2.
  rewrite dis_sym in tl_l1.
  case: {IH}(IH tl_l1 tl'_l2).
  move=> U V; by subst tl' l2.
- by rewrite H1.
- by rewrite H2.
Qed.

Lemma union_emp_inv : forall h1 h2, emp = h1 \U h2 -> h1 = emp /\ h2 = emp.
Proof.
case.
case.
- rewrite /= => Htmp.
  case => /=.
  case=> //=.
  move=> Htmp' _.
  split; by apply mk_t_pi.
- case=> hd1 hd2 tl Hord h2 H.
  suff : False by done.
  have [Hord1 Hord2] : lb X.ltA hd1 (unzip1 tl) /\ ordered X.ltA (unzip1 tl).
    by case/ordered_inv : {H} Hord.
  have H' : mk_t (cons (hd1, hd2) tl) Hord = sing hd1 hd2 \U mk_t tl Hord2.
    apply mk_t_pi; by rewrite /= add_seq_is_cons.
  have : get hd1 emp = Some hd2.
    by rewrite H H' -unionA get_union_sing_eq.
  by rewrite get_emp.
Qed.

Lemma union_inv : forall h0 h0' h1 h2,
  h0 \U h1 = h0' \U h2 -> dom h0 = dom h0' ->
  h1 # h0 -> h2 # h0' -> h0 = h0' /\ h1 = h2.
Proof.
move=> [h0 H0] [h0' H0'] [h1 H1] [h2 H2].
rewrite /disj /= => H H00' H10 H20.
apply eq_equal in H.
rewrite /equal /= in H.
case: (app_seq_reg h0 h0' h1 h2 H0 H00' H1 H2 H H10 H20) => U V; subst h0' h2.
split; by apply mk_t_pi.
Qed.

Lemma distributivity : forall h1 h2 h0, h0 # (h1 \U h2) <-> h0 # h1 /\ h0 # h2.
Proof.
move=> [h1 H1] [h2 H2] [h0 H0]; rewrite /disj /app /=; split.
- move/disP => H; split; apply/disP => x.
  + case: {H}(H x) => X Y.
    split => Z.
    * move/X : Z => Z.
      contradict Z.
      apply/inP. rewrite in_unzip1_app_seq //; by left; apply/inP.
    * apply Y.
      apply/inP. rewrite in_unzip1_app_seq //; by left; apply/inP.
  + case: {H}(H x) => X Y.
    split => Z.
    * move/X : Z => Z.
      contradict Z.
      apply/inP. rewrite in_unzip1_app_seq //; by right; apply/inP.
    * apply Y.
      apply/inP. rewrite in_unzip1_app_seq //; by right; apply/inP.
- case; move/disP=> X; move/disP=> Y; apply/disP => x.
  case: {X}(X x) => X1 X2.
  case: {Y}(Y x) => Y1 Y2.
  split=> H H'.
  + move/inP : H'; move/in_map_app_seq_inv.
    case; move/inP => H'; tauto.
  + move/inP : H; move/in_map_app_seq_inv.
    case; move/inP => H; tauto.
Qed.

Lemma disjhU h1 h2 h0 : h0 # h1 -> h0 # h2 -> h0 # (h1 \U h2).
Proof. move=> H1 H2. move: (distributivity h1 h2 h0) => X. tauto. Qed.

Lemma disjUh h1 h2 h0 : h1 # h0 -> h2 # h0 -> (h1 \U h2) # h0.
Proof. move=> H1 H2; apply disj_sym, disjhU; by apply disj_sym. Qed.

(* TODO: L/R variants? *)
Lemma disj_union_inv h1 h2 h0 : h0 # (h1 \U h2) -> h0 # h1 /\ h0 # h2.
Proof. move=> H. move: (distributivity h1 h2 h0) => X. tauto. Qed.

Lemma disj_add_map : forall h k n z,
  seq_ext.disj k (seq.map (@fst l v) ((n, z) :: h)) ->
  seq_ext.disj k (seq.map (@fst l v) (add_map X.ltA n z h)).
Proof.
elim => //.
move=> [n' z'] tl IH k n z /= H.
case: ifP => X //.
case: ifP => Y.
- move/seq_ext.disj_sym in H.
  apply disj_cons_inv in H; case: H => H _.
  by apply seq_ext.disj_sym.
- move/seq_ext.disj_sym in H.
  apply disj_cons_R; last first.
    apply disj_cons_inv in H; case: H => H _.
    case: {H}(H n') => /= H _.
    contradict H.
    by intuition.
  apply IH => /=.
  apply disj_cons_R; last first.
    case: {H}(H n) => /= H _.
    contradict H.
    by intuition.
  apply disj_cons_inv in H; case : H => H _.
  apply disj_cons_inv in H; case : H => H _.
  by apply seq_ext.disj_sym.
Qed.

Lemma disj_app_app_seq : forall l1 l2 k,
  seq_ext.disj k (seq.map fst l1 ++ seq.map (@fst l v) l2) ->
  seq_ext.disj k (map fst (app_seq l1 l2)).
Proof.
elim => [/= lk // | [n z] tl IH /= l2 k].
- move/seq_ext.disj_sym => Hdis.
  have Hdis' : seq_ext.disj (n :: nil) k.
    move=> n'.
    case: {Hdis}(Hdis n') => /= Hdis _.
    by intuition.
  apply disj_cons_inv in Hdis; case : Hdis.
  move/seq_ext.disj_sym.
  move/IH => {}IH _.
  rewrite /add_seq.
  case: ifP => X.
  + move: (unzip1_upd_seq (app_seq tl l2) n z ) => Z.
    rewrite /unzip1 in Z.
    rewrite Z.
    by apply IH.
  + apply disj_add_map.
    rewrite /= in IH *.
    apply disj_cons_R => // W.
    apply (proj1 (Hdis' n)) => //; by rewrite /=; auto.
Qed.

Lemma dis_dom_union1 : forall h1 h2 l,
  dis l (dom h1) -> dis l (dom h2) -> dis l (dom (h1 \U h2)).
Proof.
move=> [h1 H1] [h2 H2] l0 /=.
rewrite /dom /= => Hinter1 Hinter2.
by apply/disP/disj_app_app_seq/seq_ext.disj_sym/disj_app; split; apply/seq_ext.disj_sym/disP.
Qed.

Lemma dis_dom_union2 : forall h1 h2 l,
  dis l (dom (h1 \U h2)) -> dis l (dom h1) /\ dis l (dom h2).
Proof.
move=> [h1 H1] [h2 H2] k /=.
rewrite /dom /=; move/disP => Hdis.
split; apply/disP.
- move=> x; split=> Hx abs.
  + apply: (proj1 (Hdis x) Hx).
    apply/inP.
    apply in_unzip1_app_seq.
    left.
    by apply/inP.
  + apply: (proj1 (Hdis x) abs).
    apply/inP.
    apply in_unzip1_app_seq.
    left.
    by apply/inP.
- move=> x; split=> Hx abs.
  + apply: (proj1 (Hdis x) Hx).
    apply/inP.
    apply in_unzip1_app_seq.
    right.
    by apply/inP.
  + apply: (proj1 (Hdis x) abs).
    apply/inP.
    apply in_unzip1_app_seq.
    right.
    by apply/inP.
Qed.

Lemma dis_dom_union h1 h2 l : dis l (dom (h1 \U h2)) = dis l (dom h1) && dis l (dom h2).
Proof.
apply/idP/idP.
- move/dis_dom_union2. by move/andP.
- case/andP. by apply dis_dom_union1.
Qed.

Lemma elts_union_sing_Perm' : forall d x rx, x \notin dom d ->
  Permutation ((x, rx) :: elts d) (elts (sing x rx \U d)).
Proof.
case=> /=.
elim.
- move=> _ x rx _; by apply Permutation_refl.
- move=> [hd hd'] /= tl IH.
  rewrite /dom /=.
  case/ordered_inv => H1 H2 x rx.
  rewrite in_cons negb_or.
  case/andP => H3 H4 /=.
  rewrite /add_seq /unzip1 /= in_cons (negbTE H3) /= (negbTE H4) /=.
  case: ifP => X.
  + rewrite /=; by apply Permutation_refl.
  + rewrite /= (_ : (x, rx) :: _ = ((x, rx) :: nil) ++ (hd, hd') :: tl) //.
    apply Permutation_sym, Permutation_cons_app => /=.
    apply Permutation_sym.
    move: (IH H1 x rx H4).
    by rewrite /add_seq (negbTE H4).
Qed.

Lemma elts_union_sing_Perm l d x rx : Permutation l (elts d) ->
  ~ List.In x (unzip1 l) ->
  Permutation ((x, rx) :: l) (elts (sing x rx \U d)).
Proof.
move=> H_k_d Hnotin.
eapply Permutation.perm_trans; last first.
- apply elts_union_sing_Perm'.
  move: H_k_d.
  move/Permutation_sym.
  move/(Permutation.Permutation_map fst).
  move/(Permutation_in x) => X.
  apply/inP.
  contradict Hnotin.
  by apply X.
- rewrite /=; by apply perm_skip.
Qed.

(** deletion of several elements *)

Definition del_seq (d : seq l) (k : seq (l * v)) := filter [pred x | x.1 \notin d] k.

Lemma notin_unzip1_del_seq : forall l1 l2 x, x \in l1 -> x \notin unzip1 (del_seq l1 l2).
Proof.
elim=> // h1 t1 IH l2 x.
rewrite in_cons.
case/orP.
- move/eqP => X; subst h1.
  rewrite /del_seq /unzip1 /=.
  apply/mapP => Y.
  case: Y => y Y1 Y2.
  subst x.
  by rewrite mem_filter /= inE eqxx in Y1.
- move=> Hx.
  move: {IH}(IH l2 _ Hx) => IH.
  rewrite /del_seq /unzip1 /=.
  apply/mapP => Y.
  case: Y => y Y1 Y2.
  subst x.
  rewrite mem_filter in Y1.
  case/andP : Y1 => Y1 Y3.
  rewrite /= in_cons negb_or in Y1.
  case/andP : Y1 => Y1 Y4.
  by rewrite Hx in Y4.
Qed.

Lemma notin_unzip1_del_seq_app : forall l d1 d2 x,
  x \notin unzip1 (del_seq d1 l) ->  x \notin unzip1 (del_seq d2 l) ->
  x \notin unzip1 (del_seq (d1 ++ d2) l).
Proof.
elim=> // hd tl IH d1 d2 x /=.
destruct hd as [h1 h2] => /=.
case/boolP : (h1 \notin d1) => X.
- rewrite /= in_cons.
  rewrite negb_or.
  case/andP => H1 H2.
  case: ifP => Y.
  + rewrite /= in_cons.
    rewrite negb_or.
    case/andP => H3 H4.
    rewrite mem_cat (negbTE X) (negbTE Y) /=.
    rewrite in_cons.
    rewrite negb_or.
    rewrite H1 /=.
    exact: IH.
  + move => H3.
    rewrite mem_cat (negbTE X) Y /=.
    exact: IH.
- move => H1.
  case/boolP : (h1 \notin d2) => Y.
  + rewrite /= in_cons.
    rewrite negb_or.
    case/andP => H2 H3.
    rewrite mem_cat negb_or (negbTE X) (negbTE Y) /=.
    exact: IH.
  + move=> H2.
    rewrite mem_cat negb_or (negbTE X) /=.
    exact: IH.
Qed.

Lemma del_seq_upd_seq : forall k d n w, n \in d -> del_seq d (upd_seq n w k) = del_seq d k.
Proof.
elim=> //.
move=> [hd hd'] tl IH d n w H /=.
case: ifP => X.
- move/eqP in X; subst.
  have H' : hd \notin d = false by apply/negP; apply/negP.
  by rewrite H' /del_seq /= H'.
- case: ifP => Y; by rewrite /= Y IH.
Qed.

Lemma del_seq_invariant k ns : dis (unzip1 k) ns -> del_seq ns k = k.
Proof.
move=> H.
rewrite /del_seq.
eapply trans_eq; last by apply filter_predT.
apply: eq_in_filter.
case=> x1 x2 /= X.
move/disP : H.
case/(_ x1) => H _.
apply/inP.
apply H.
apply/inP.
apply/mapP; by exists (x1, x2).
Qed.

Lemma ordered_del_seq : forall k, ordered X.ltA (unzip1 k) ->
  forall d, ordered X.ltA (unzip1 (del_seq d k)).
Proof.
move=> k H d.
rewrite /del_seq (@unzip1_filter _ _ k (fun n => ~~ (n \in d))).
by apply ordered_filter.
Qed.

Definition difs h l := mk_t _ (ordered_del_seq (elts h) (prf h) l).
Local Notation "k '\D\' m" := (difs k m).

Lemma filter_add_seq1 : forall k (Hk : ordered X.ltA (unzip1 k)) a b p,
  a \notin unzip1 k ->
  p a = true ->
  filter (fun x => p (fst x)) (add_seq a b k) =
  add_seq a b (filter (fun x => p (fst x)) k).
Proof.
elim.
  move=> _ a b p /= _ -> //.
move=> [hk1 hk2] /= tk IH.
case/ordered_inv=> Htk Hhk a b p.
rewrite in_cons negb_or.
case/andP=> H1 H2 Hp.
rewrite {1}/add_seq.
have -> : a \in unzip1 (cons (hk1, hk2) tk) = false.
  rewrite /dom /= in_cons.
  move/negbTE : H1 => H1.
  rewrite H1 /=.
  rewrite /dom in H2.
  by apply/negP; apply/negP.
rewrite /=.
case/boolP : (X.ltA a hk1) => X.
- rewrite [cons (hk1, hk2) tk]lock /= -lock.
  rewrite Hp /= add_seq_is_cons //.
  case/boolP : (p hk1) => Y.
  * rewrite /=.
    apply/andP; split => //.
    rewrite unzip1_filter.
    apply lb_incl.
    rewrite /dom in Hhk.
    apply lb_trans with hk1 => //; by ord_pro.
  * rewrite unzip1_filter.
    apply lb_incl.
    rewrite /dom in Hhk.
    apply lb_trans with hk1 => //; by ord_pro.
- move/negbTE in H1.
  rewrite H1 /=.
  case/boolP : (p hk1) => Y.
  * rewrite /add_seq.
    have XX : a \in unzip1 (cons (hk1, hk2) (filter (fun x => p x.1) tk)) = false.
      rewrite /unzip1 in H2.
      rewrite /unzip1 /= in_cons H1 /= -/(unzip1 _) unzip1_filter.
      apply/negP.
      move/negP in H2.
      contradict H2.
      rewrite mem_filter in H2.
      by case/andP : H2.
    rewrite XX /= H1 (negbTE X).
    move: (IH Htk a b p H2 Hp).
    rewrite /add_seq.
    have -> : a \in unzip1 (filter (fun x : l * v => p x.1) tk) = false.
      rewrite /dom /= in_cons in XX.
      apply negbT in XX.
      rewrite negb_or in XX.
      case/andP : XX => _ XX.
      apply/negP.
      by move/negP : XX.
    suff : a \in unzip1 tk = false. by move=> -> ->.
    apply/negP.
    by move/negP : H2.
  * move: (IH Htk a b p H2 Hp).
    rewrite {1}/add_seq.
    suff : a \in unzip1 tk = false by move=> ->.
    apply/negP.
    by move/negP : H2.
Qed.

Lemma filter_add_seq2 : forall k (Hk : ordered X.ltA (unzip1 k)) a b p,
  a \in unzip1 k ->
  p a = true ->
  filter (fun x => p (fst x)) (add_seq a b k) = 
  add_seq a b (filter (fun x => p (fst x)) k).
Proof.
elim.
  move=> _ a b p /= _ -> //.
move=> [hk1 hk2] /= tk IH.
case/ordered_inv=> Htk Hhk a b p.
rewrite in_cons.
case/orP.
- move/eqP => X; subst hk1 => Hpa.
  rewrite Hpa.
  rewrite {1}/add_seq.
  have -> : a \in unzip1 (cons (a, hk2) tk) = true.
    by rewrite /dom /= in_cons eqxx.
  rewrite /= eqxx /= Hpa /add_seq.
  have -> : a \in unzip1 (cons (a, hk2) (filter (fun x => p x.1) tk)) = true.
    by rewrite /dom /= in_cons eqxx.
  by rewrite /= eqxx. 
- move=> Ha_tk Hpa.
  rewrite {1}/add_seq.
  have -> : a \in unzip1 (cons (hk1, hk2) tk) = true.
    by rewrite /dom /= in_cons Ha_tk orbC.
  rewrite /=.
  case/boolP : (a == hk1) => Y.
  + move/eqP in Y.
    subst hk1.
    exfalso.
    move: Ha_tk.
    apply/negP.
    by rewrite (mem_lb X.ltA_irr).
  + move/negbTE in Y.
    case/boolP : (p hk1) => Z.
    * rewrite /= /add_seq.
      have -> : a \in unzip1 (cons (hk1, hk2) (filter (fun x : l * v => p x.1) tk)) = true.
        by rewrite /unzip1 /= in_cons -/(unzip1 _) unzip1_filter Y /= mem_filter Hpa.
      rewrite /= Y.
      f_equal.
      move: (IH Htk a b p Ha_tk Hpa).
      rewrite /add_seq Ha_tk.
      have -> : a \in unzip1 (filter (fun x  => p x.1) tk) = true.
        by rewrite /unzip1 /= -/(unzip1 _) unzip1_filter mem_filter Hpa.
      by rewrite Z => ->.
    * move: (IH Htk a b p Ha_tk Hpa) => /=; rewrite (negbTE Z).
      by rewrite {1}/add_seq Ha_tk.
Qed.
      
Lemma filter_add_seq : forall k (Hk : ordered X.ltA (unzip1 k)) a b p,
  p a = true ->
  filter (fun x => p (fst x)) (add_seq a b k) = 
  add_seq a b (filter (fun x => p (fst x)) k).
Proof.
move=> k HK a b p Hpa.
case/boolP : (a \in unzip1 k) => X.
by apply filter_add_seq2.
by apply filter_add_seq1.
Qed.

Lemma filter_add_seq' : forall k (Hk : ordered X.ltA (unzip1 k)) a b p,
  p a = false ->
  filter (fun x => p (fst x)) (add_seq a b k) = 
  filter (fun x => p (fst x)) k.
Proof.
elim.
move=> _ a b p Hp.
by rewrite /= Hp.
move=> [h1 h2] /= tl IH Hord a b p Hpa.
rewrite /add_seq.
case/boolP : (a \in unzip1 (cons (h1, h2) tl)) => X.
- rewrite /=.
  case/boolP : (a == h1) => Y.
  + rewrite /=.
    move/eqP : Y => Y; subst a.
    by rewrite Hpa.
  + rewrite /=.
    case: ifP => Z.
    * f_equal.
      case/ordered_inv : Hord => Hord Hord'.
      move: {IH}(IH Hord a b p Hpa) => IH.
      rewrite /add_seq in IH.
      have XXXX : a \in unzip1 tl = true.
        rewrite /dom /= in_cons (negbTE Y) /= in X.
        by rewrite X.
      by rewrite XXXX in IH.
    * case/ordered_inv : Hord => Hord Hord'.
      move: {IH}(IH Hord a b p Hpa) => IH.
      rewrite /add_seq in IH.
      have XXXX : a \in unzip1 tl = true.
        rewrite /= in_cons (negbTE Y) /= in X.
        by rewrite X.
      by rewrite XXXX in IH.
- move/negbTE : X => X.
  rewrite /=.
  case/boolP : (X.ltA a h1) => Y.
  + rewrite /= Hpa.
    by case: ifP.
  + move/negbTE in Y.
    case/boolP : (a == h1) => Z.
    * move/eqP in Z.
      subst h1.
      by rewrite Hpa /= Hpa.
    * move/negbTE : Z => Z.
      rewrite /=.
      case: ifP => U.
      - f_equal.
        case/ordered_inv : Hord => Hord Hord'.
        move: {IH}(IH Hord a b p Hpa) => IH.
        rewrite /add_seq in IH.
        have XXXX : a \in unzip1 tl = false.
          rewrite /= in_cons Z /= in X.
          by rewrite X.
        by rewrite XXXX in IH.
      - case/ordered_inv : Hord => Hord Hord'.
        move: {IH}(IH Hord a b p Hpa) => IH.
        rewrite /add_seq in IH.
        have XXXX : a \in unzip1 tl = false.
          rewrite /= in_cons Z /= in X.
          by rewrite X.
        by rewrite XXXX in IH.
Qed.

Lemma filter_app_seq : forall k1 (Hk1 : ordered X.ltA (unzip1 k1))
  k2 (Hk2 : ordered X.ltA (unzip1 k2)) (p : pred l),
  filter (fun x => p (fst x) ) (app_seq k1 k2) =
  app_seq (filter (fun x => p (fst x)) k1) (filter (fun x => p (fst x)) k2).
Proof.
elim => //.
case=> h11 h12 t1 IH_k1 /= Hord_k1 k2 Hord_k2 p.
case/ordered_inv : Hord_k1 => Hord_k1 Hord_k1'.
case: ifP => X.
- rewrite filter_add_seq //; last by apply ordered_app_seq.
  by rewrite IH_k1.
- rewrite -IH_k1 // filter_add_seq' //.
  by apply ordered_app_seq.
Qed.

Lemma dis_difs s l : dis (dom s) l -> s \D\ l = s.
Proof.
case: s => /= s Hs.
rewrite /difs /= /dom /= => sl.
apply mk_t_pi.
by rewrite del_seq_invariant.
Qed.

Lemma difs_union : forall h1 h2 k, (h1 \U h2) \D\ k = (h1 \D\ k) \U (h2 \D\ k).
Proof.
move=> [h1 Hh1] [h2 Hh2] /= k; rewrite /difs /=; apply mk_t_pi => /=.
by rewrite /del_seq (filter_app_seq _ Hh1 _ Hh2 (fun x : l => x \notin k)).
Qed.

Lemma difs_union_L : forall h1 h2 k, dis (dom h2) k ->
  (h1 \U h2) \D\ k = (h1 \D\ k) \U h2.
Proof. move=> h1 h2 k h2k; by rewrite difs_union (dis_difs h2). Qed.

Lemma difs_union_R : forall h1 h2 k, dis (dom h1) k ->
  (h1 \U h2) \D\ k = h1 \U (h2 \D\ k).
Proof.
Proof. move=> h1 h2 k h1k; by rewrite difs_union (dis_difs h1). Qed.

Lemma difs_self : forall k, k \D\ dom k = emp.
Proof.
case=> k Hk /=; apply mk_t_pi; rewrite /del_seq /dom /=.
transitivity (filter pred0 k); last by rewrite filter_pred0.
apply eq_in_filter => -[x1 x2] x_k /=; apply/mapP => /=; by exists (x1, x2).
Qed.

Lemma difs_upd : forall k n w d, n \in d -> upd n w k \D\ d = k \D\ d.
Proof.
move=> [k Hk] n w d H; rewrite /difs /=; by apply mk_t_pi, del_seq_upd_seq.
Qed.

Lemma disj_difs : forall h1 h2, h1 # h2 -> forall d, h1 # h2 \D\ d.
Proof.
move=> [h1 H1] [h2 H2] /=; rewrite /disj /= => H d.
by rewrite /del_seq (unzip1_filter h2 (fun n => ~~ mem d n)) dis_sym dis_filter // dis_sym.
Qed.

Lemma disj_difs' : forall h1 h2 d, inc (dom h1) d -> h1 # h2 \D\ d.
Proof.
move=> [h1 H1] [h2 H2] /= d Hd.
rewrite /dom /= in Hd.
rewrite /disj /= /del_seq /=.
apply/(dis_inc_L _ Hd).
rewrite (unzip1_filter h2 (fun n => ~~ (n \in d))).
by apply dis_filter_right.
Qed.

Lemma get_seq_del_seq : forall k w d, w \in d -> get_seq w (del_seq d k) = None.
Proof.
elim=> //; move=> [h1 h2] tl IH w d Hw /=.
case: ifP => X.
- rewrite /= get_seq_cons'.
  by apply IH.
  move=> ?; subst h1; by rewrite Hw in X.
- by apply IH.
Qed.

Lemma get_seq_del_seq' : forall k x d, x \notin d -> get_seq x (del_seq d k) = get_seq x k.
Proof.
elim=> //; case=> h1 h2 tl IH x d Hx /=.
case: ifP => X.
- rewrite /=.
  case/boolP : (x == h1) => Y.
  + move/eqP : Y => Y; subst h1.
    by rewrite !get_seq_cons.
  + rewrite get_seq_cons'; last first.
      move/eqP : Y; auto.
    rewrite get_seq_cons'; last first.
      move/eqP : Y; auto.
    by apply IH.
- rewrite /= get_seq_cons'; last first.
    move=> Y; subst h1; by rewrite Hx in X.
  by apply IH.
Qed.

Lemma get_difs : forall k x d, x \notin d -> get x (k \D\ d) = get x k.
Proof. move=> [k Hk] x d Hx. rewrite /get /difs /=. by apply get_seq_del_seq'. Qed.

Lemma get_difs_None : forall k x d, x \in d -> get x (k \D\ d) = None.
Proof. move=> k x d Hx. rewrite /get /difs /= get_seq_del_seq //. Qed.

Lemma dom_difs_del : forall k d, dom (k \D\ d) = filter (predC (mem d)) (dom k).
Proof.
case=> k Hk d.
rewrite /dom /= /del_seq.
apply trans_eq with (filter (fun x : l => x \notin d) (map (fun x => fst x) k)); last by done.
by rewrite filter_map.
Qed.

Lemma mem_dom_difs : forall l x k, x \in dom l -> x \notin k -> x \in dom (l \D\ k).
Proof.
case.
elim=> //= h t IH o x k.
rewrite /dom /= in_cons.
case/orP => [/eqP ->{x} -> | xt xk ].
  apply/mapP.
  exists h => //; by rewrite in_cons eqxx.
case/ordered_inv : o => o1 o2.
move: (IH o1 x k xt xk) => {IH} /=.
rewrite /dom /= => IH.
case: ifP => //- hk.
by rewrite in_cons IH orbT.
Qed.

Lemma difsK s l : s \D\ l \D\ l = s \D\ l.
Proof.
case: s => /= s Hs; rewrite /difs /=; apply mk_t_pi => /=.
rewrite /del_seq -filter_predI /=.
by apply eq_filter => -[x1 x2] /=; rewrite andbb.
Qed.

(* xxx *)
Lemma add_seq_del_seq k x v : ordered X.ltA (unzip1 k) ->
  add_seq x v (del_seq [:: x] k) = add_seq x v k.
Proof.
elim: k x v => // -[h1 h2] /= t IH x v /ordered_inv[Ht h1t].
rewrite inE.
case: ifPn => h1x.
  rewrite /add_seq.
  rewrite ifF; last first.
    apply/negbTE/mapP => -[] -[x1 x2] /=.
    rewrite in_cons => /orP[/eqP [-> _]|]; first by apply/eqP; rewrite eq_sym.
    rewrite mem_filter /= mem_seq1 => /andP[/eqP/nesym]; tauto.
  rewrite /unzip1 [map _ _]/= in_cons eq_sym (negbTE h1x) orFb.
  case: ifPn.
    case/mapP => -[x1 x2] xt; rewrite [in X in X -> _]/= => ?; subst x1.
    rewrite /= eq_sym (negbTE h1x) ifF; last first.
      apply/negbTE.
      rewrite flip //; try ord_pro.
      apply: (mem_lt_lb _ _ _ h1t).
      apply/mapP; by exists (x, x2).
    congr cons.
    move: (IH x v Ht).
    rewrite /add_seq.
    rewrite ifF; last first.
      apply/negbTE.
      apply/mapP => -[] -[x1' x2'].
      rewrite mem_filter /= mem_seq1 => /andP[/eqP/nesym]; tauto.
    rewrite ifT //.
    by apply/mapP; by exists (x, x2).
  move=> xt.
  rewrite (_ : del_seq _ _ = t) //.
  rewrite /del_seq -[RHS](filter_predT t).
  apply eq_in_filter => -[y1 y2] yt /=.
  rewrite mem_seq1; apply/eqP => ?; subst y1.
  move/negP : xt; apply.
  apply/mapP; by exists (x, y2).
rewrite IH //.
rewrite negbK in h1x.
move/eqP in h1x.
subst h1.
by rewrite {2}/add_seq in_cons /= eqxx /= add_seq_is_cons.
Qed.

(* xxx *)
Lemma union_sing_difs x v s : sing x v \U (s \D\ [:: x]) = sing x v \U s.
Proof.
case: s => k Hk /=.
rewrite /difs /= /union /=.
apply mk_t_pi => /=.
by apply add_seq_del_seq.
Qed.

(** projection *)

Definition
 proj_seq (k : seq (l * v)) (d : seq l) : seq (l * v) := filter (fun x => x.1 \in d) k.

Lemma proj_seq_nil : forall d, proj_seq [::] d = [::]. by elim. Qed.

Lemma proj_seq_nil' : forall k, proj_seq k [::] = [::]. by elim. Qed.

Lemma proj_seq_cons : forall l2 h1 t1,
  h1 \notin (unzip1 l2) -> proj_seq l2 (cons h1 t1) = proj_seq l2 t1.
Proof.
elim=> //.
move=> [h2 h2'] t2 IH h1 t1 H.
rewrite /proj_seq.
by apply filter_in_cons.
Qed.

Lemma in_proj_seq_inv : forall d k x, x \in proj_seq k d -> x \in k.
Proof. move=> d j x. rewrite /proj_seq mem_filter. case/andP => //. Qed.

Lemma get_seq_proj_seq_None : forall k d n, n \notin d -> get_seq n (proj_seq k d) = None.
Proof.
elim=> //.
move=> [hd hd'] /= tl IH d n Hn.
case: ifP => X.
  rewrite /= get_seq_cons'.
    by auto.
  move=> Y; subst.
  by rewrite X in Hn.
by apply IH.
Qed.

Lemma get_seq_proj_seq : forall k d n, n \in d -> get_seq n (proj_seq k d) = get_seq n k.
Proof.
elim=> //.
move=> hd tl IH d n Hnd.
rewrite /=.
case: ifP => X.
- rewrite /get_seq /=.
  case/boolP : (n == hd.1) => Y //.
  by move: {IH}(IH d _ Hnd).
- rewrite (IH d _ Hnd).
  destruct hd as [hd1 hd2].
  rewrite get_seq_cons' //.
  rewrite /= in X.
  move=> Y; subst n.
  by move/negP : X.
Qed.

Lemma dis_proj_seq (l1 l2 : seq (l * v)) :
  dis (unzip1 l1) (unzip1 l2) -> proj_seq l1 (unzip1 l2) = [::].
Proof.
move: l2 l1. elim.
- rewrite /= => l1 _; rewrite /proj_seq.
  by apply filter_pred0.
- elim=> hd tl l2 IHl2 l1 /= Hdisj.
  rewrite /proj_seq /=.
  have X : ~~ (hd \in unzip1 l1).
    apply/negP.
    rewrite dis_sym /= in Hdisj.
    move: Hdisj.
    by case: ifP.
  rewrite filter_in_cons //.
  apply IHl2.
  move: Hdisj.
  rewrite dis_sym /=.
  case: ifP => // _.
  by rewrite dis_sym.
Qed.

Lemma ordered_proj_seq : forall k, ordered X.ltA (unzip1 k) ->
  forall d, ordered X.ltA (unzip1 (proj_seq k d)).
Proof.
move=> k Hk d.
move: (unzip1_filter k (fun x => x \in d)).
rewrite /proj_seq /unzip1 => ->.
by apply: ordered_filter.
Qed.

Definition proj k d : t := mk_t _ (ordered_proj_seq _ (prf k) d).
Local Notation "k '|P|' m" := (proj k m).

Lemma proj_emp k : emp |P| k = emp.
Proof. by apply mk_t_pi. Qed.

Lemma proj_nil : forall k, k |P| [::] = emp.
Proof. case=> k Hk; rewrite /proj /=; by apply mk_t_pi, proj_seq_nil'. Qed.

Lemma proj_seq_proj_seq : forall k (Hk : ordered X.ltA (unzip1 k))
  d d', inc d' d ->
  proj_seq (proj_seq k d) d' = proj_seq k d'.
Proof.
move=> k Hk d d' dd'.
rewrite /proj_seq.
rewrite -filter_predI.
apply eq_in_filter => x Hx /=.
apply/idP/idP.
- by case/andP.
- move=> Hx1; rewrite Hx1 /=.
  move/incP' : dd'; exact.
Qed.

Lemma proj_proj : forall h d d', inc d' d -> (h |P| d) |P| d' = h |P| d'.
Proof.
case=> k Hk d d' dd'.
rewrite /proj /=.
apply mk_t_pi.
by apply proj_seq_proj_seq.
Qed.

Lemma dom_proj_sing : forall k n, n \in dom k -> dom (k |P| [:: n]) = [:: n].
Proof.
case=> k Hk n.
rewrite /dom /= => Hn.
rewrite /proj_seq /= unzip1_filter.
apply: filter_mem_cons => //.
by apply (ordered_uniq X.ltA_irr).
Qed.

Lemma cdom_proj_sing : forall (k : t) (n : l) v, get n k = Some v ->
  cdom (k |P| [:: n]) = [:: v].
Proof.
case=> k Hk b v.
move/get_Some_in => /=.
case/(nthP (b,v)) => i ik Hik.
rewrite /cdom /= /proj_seq.
have Hk' : k = take i k ++ (b, v) :: drop i.+1 k.
  by rewrite -{1}(cat_take_drop i k) -Hik -drop_nth.
rewrite Hk' filter_cat /= in_cons eqxx /= /unzip2 map_cat /=.
set fil1 := (fun x => _).
have -> : filter fil1 (take i k) = filter pred0 (take i k).
  apply eq_in_filter => x Hx.
  rewrite /fil1 in_cons in_nil orbC /=.
  apply/negbTE.
  rewrite X.ltA_total.
  apply/orP.
  left.
  rewrite Hk' /unzip1 map_cat in Hk.
  move/ordered_app_inv_ltA : Hk.
  apply.
  - apply/mapP; by exists x.
  - by rewrite /= in_cons eqxx.
rewrite filter_pred0 /=.
f_equal.
have -> : filter fil1 (drop i.+1 k) = filter pred0 (drop i.+1 k).
  apply eq_in_filter => x Hx.
  rewrite /fil1 in_cons in_nil orbC /=.
  apply/negP/negP.
  rewrite X.ltA_total.
  apply/orP.
  right.
  rewrite Hk' /unzip1 -cat_rcons rcons_app map_cat in Hk.
  move/ordered_app_inv_ltA : Hk.
  apply.
  - by rewrite map_cat mem_cat in_cons /= eqxx orbC.
  - apply/mapP; by exists x.
by rewrite filter_pred0.
Qed.

Lemma inc_dom_proj : forall d k, inc (dom (k |P| d)) d.
Proof.
elim=> [k|hd tl H [k Hk]]; first by rewrite proj_nil.
apply/incP' => x.
case/mapP=> X X_in_proj x_X1; subst x.
rewrite /proj_seq mem_filter in X_in_proj.
by case/andP : X_in_proj.
Qed.

Lemma inc_dom_proj_dom : forall h d, inc (dom (h |P| d)) (dom h).
Proof.
case=> k Hk d /=.
by rewrite /dom /= /proj_seq /= /= /unzip1 -filter_map inc_filter_L // inc_refl.
Qed.

Lemma dom_proj_exact' : forall k d, ordered X.ltA d -> inc d k ->
  ordered X.ltA k -> filter (mem d) k = d.
Proof.
elim=> [d _|hd_k tl_k IH d Hord_d Hincl]; first by move/inc_nil_inv.
case/ordered_inv=> Hord_tl_k H_hd_k_tl_k.
destruct d as [|hd_d tl_d] => //.
- transitivity (filter pred0 (cons hd_k tl_k)); last by rewrite filter_pred0.
  apply eq_in_filter => x Hx /=.
  by rewrite in_nil.
- case/ordered_inv: Hord_d => Hord_tl_d H_hd_d_tl_d.
  rewrite inc_cons_L in Hincl.
  case/andP : Hincl => Hincl1 Hincl2.
  rewrite in_cons in Hincl2.
  case/orP : Hincl2 => Hincl2.
  + (* d et k ont la meme tete *) move/eqP : Hincl2 => Hincl2.
    subst hd_d.
    rewrite /= in_cons eqxx /=; f_equal.
    transitivity (filter (mem tl_d) tl_k).
    apply eq_in_filter => x Hx /=.
    rewrite in_cons.
    case/boolP : (x == hd_k) => K.
    rewrite /=.
    move/eqP : K => ?; subst x.
    apply (mem_lb X.ltA_irr) in H_hd_k_tl_k.
    by rewrite Hx in H_hd_k_tl_k.
    by rewrite orFb.
    apply IH => //.
    apply (mem_lb X.ltA_irr) in H_hd_d_tl_d.
    by apply (inc_cons_R_inv H_hd_d_tl_d) in Hincl1.
  + (* la tete de d est plus loin dans k *) rewrite /=.
    rewrite in_cons.
    move: (mem_lb X.ltA_irr H_hd_k_tl_k) => H_hd_k_tl_k'.
    have H_hd_k_Hd_d : hd_k != hd_d.
      apply/negP.
      move/eqP => ?; subst hd_k.
      by rewrite Hincl2 in H_hd_k_tl_k'.
    rewrite (negbTE H_hd_k_Hd_d) /=.
    have K : hd_k \notin tl_d.
      apply/negP => abs.
      have abs1 : X.ltA hd_k hd_d by eapply mem_lt_lb; eauto.
      have abs2 : X.ltA hd_d hd_k by eapply mem_lt_lb; eauto.
      move: (X.ltA_trans abs1 abs2).
      by rewrite X.ltA_irr.
    rewrite (negbTE K) IH //.
    by constructor.
    rewrite /= Hincl2.
    by apply (inc_cons_R_inv K) in Hincl1.
Qed.

Lemma dom_proj_exact : forall h d, ordered X.ltA d -> inc d (dom h) -> dom (h |P| d) = d.
Proof.
case=> k Hk d.
rewrite /dom /= /proj_seq /unzip1 -filter_map.
move=> Hord Hinc.
rewrite /unzip1 in Hk.
by apply (dom_proj_exact' (map (fun x => x.1) k) _ Hord Hinc Hk).
Qed.

(* TODO: clean *)
Lemma size_dom_proj_exact' : forall (A : eqType) (k d : seq A),
  uniq k -> uniq d -> inc d k -> size (filter (mem d) k) = size d.
Proof.
move=> A.
move => k.
move Hn : (size k) => n.
move: n k Hn.
elim; first by case=> // _ [].
move=> n IH [|hd tl] // [sz_tl] d /=.
case/andP => hd_tl u_tl u_d Hinc.
case: ifP => hd_d.
- have [d' Hd'] : exists d', perm_eq d (hd :: d').
    (* TODO: pull out a lemma out of this? *)
    exists (filter (predC (pred1 hd)) d).
    apply perm_trans with (filter (pred1 hd) d ++ filter (predC (pred1 hd)) d).
    rewrite perm_sym.
    apply/permPl.
    by apply perm_filterC.
    rewrite -cat1s.
    rewrite perm_cat2r.
    suff : filter (pred1 hd) d = cons hd [::]. by move=> ->; apply perm_refl.
    rewrite -(filter_mem_cons u_d hd_d).
    apply eq_filter => x /=.
    by rewrite in_cons in_nil orbC.
  have {}Hinc : inc (cons hd d') (cons hd tl).
    (* TODO: pull out a lemmas out of this? *)
    rewrite /= in_cons eqxx /=.
    apply/incP' => x Hx.
    move/incP' in Hinc; apply/Hinc.
    move/perm_mem in Hd'.
    by rewrite Hd' in_cons Hx orbC.
  rewrite inc_cons_L in Hinc.
  case/andP : Hinc => Hinc1 Hinc2.
  transitivity (size (cons hd d')).
  + rewrite /=.
    f_equal.
    transitivity (size (filter (mem d') tl)).
    * f_equal.
      apply eq_in_filter => x Hx /=.
      case/boolP : (x \in d') => x_d'.
      * apply/negP => abs.
        have {}abs : ~ x \in cons hd d'.
          contradict abs.
          by move/perm_mem : Hd' => ->.
        rewrite in_cons in abs.
        move/negP : abs.
        rewrite negb_or.
        by rewrite x_d' andbC.
      * apply/negP => abs.
        have {}abs : x \in cons hd d'.
          by move/perm_mem : Hd' => <-.
        rewrite in_cons in abs.
        case/orP : abs => abs.
        - move/eqP : abs => ?; subst x.
          by rewrite Hx in hd_tl.
        - by rewrite abs in x_d'.
    * apply IH => //.
      - apply perm_uniq in Hd'.
        rewrite /= u_d in Hd'.
        symmetry in Hd'.
        by case/andP : Hd'.
      - apply inc_cons_R_inv in Hinc1 => //.
        apply/negP => abs.
        apply perm_uniq in Hd'.
        by rewrite /= u_d abs /= in Hd'.
  + apply perm_size.
    by rewrite perm_sym.
- apply IH => //.
  apply inc_cons_R_inv in Hinc => //.
  by apply/negbT.
Qed.

Lemma size_dom_proj_exact : forall h d, uniq d -> inc d (dom h) -> size (dom (h |P| d)) = size d.
Proof.
case=> k Hk d u_d.
rewrite /dom /= /proj_seq /= => Hd.
rewrite /unzip1 -filter_map size_dom_proj_exact' //.
by apply (ordered_uniq X.ltA_irr).
Qed.

Lemma dom_proj_cons : forall k n d, n \notin dom k -> k |P| n :: d = proj k d.
Proof.
move=> [k Hk] n d /= H.
rewrite /dom /= in H.
rewrite /proj /=.
apply: mk_t_pi.
by rewrite /proj_seq filter_in_cons.
Qed.

Lemma in_dom_proj : forall x d h, x \in d -> x \in dom h -> x \in dom (h |P| d).
Proof.
move=> x d [k Hk] x_in_d x_in_k.
rewrite /dom /= /proj_seq /= /unzip1 -filter_map mem_filter.
apply/andP; split; first by done.
by rewrite /dom /= /proj_seq /= in x_in_k.
Qed.

Lemma in_dom_proj_inter : forall k d m, m \in dom (k |P| d) -> m \in dom k /\ m \in d.
Proof.
case=> k Hk d m.
rewrite /dom /=.
case/mapP => x Hx ?; subst m.
rewrite /proj_seq mem_filter in Hx.
case/andP : Hx => Hx1 Hx2.
rewrite Hx1; split; last by done.
by move/(map_f (fun x => fst x)) : Hx2.
Qed.

Lemma filter_upd_seq : forall k p w P, P p = false ->
  filter (fun x : l * v => P (fst x)) (upd_seq p w k) =
  upd_seq p w (filter (fun x : l * v => P (fst x)) k).
Proof.
elim=> //.
move=> [h1 h2] tl IH p w P /= Hp.
case/boolP : (p == h1) => X.
- rewrite /=.
  move/eqP : X => X.
  subst h1.
  rewrite Hp upd_seq_invariant //.
  case/boolP : (p \in unzip1 tl) => Y.
  + rewrite unzip1_filter mem_filter.
    apply/negP.
    by rewrite negb_and Hp.
  + rewrite unzip1_filter mem_filter.
    apply/negP; by rewrite negb_and Hp.
- case/boolP : (P h1) => Z.
  + rewrite /= Z (negbTE X).
    f_equal.
    by apply IH.
  + rewrite /= (negbTE Z); by apply IH.
Qed.

Lemma filter_upd_seq' : forall k p w P, P p = true ->
  filter (fun x : l * v => P (fst x)) (upd_seq p w k) =
  upd_seq p w (filter (fun x : l * v => P (fst x)) k).
Proof.
elim=> //; case=> h1 h2 tl IH p w P /= Hp.
case/boolP : (p == h1) => X.
- rewrite /=.
  move/eqP : X => X.
  subst h1.
  by rewrite Hp /= eqxx.
- move/negbTE : X => X.
  case/boolP : (P h1) => Z.
  + rewrite /= Z X.
    f_equal.
    by apply IH.
  + move/negbTE : Z => Z.
    rewrite /= Z.
    by apply IH.
Qed.

Lemma proj_upd_notin : forall d k p w, p \notin d -> upd p w k |P| d = upd p w (k |P| d).
Proof.
elim=> [k p w|hd tl IH [k Hk] /= p w Hp].
- by rewrite !proj_nil upd_emp.
- rewrite /proj /upd /=.
  apply mk_t_pi.
  rewrite /proj_seq.
  apply filter_upd_seq.
  apply/negP.
  by apply/negP.
Qed.

Lemma proj_upd_in : forall d k p w, p \in d -> upd p w k |P| d = upd p w (k |P| d).
Proof.
elim=> [k p w |hd tl IH [k Hk] /= p w Hp].
- by rewrite !proj_nil upd_emp.
- rewrite /proj /upd /=.
  apply mk_t_pi.
  rewrite /proj_seq.
  apply filter_upd_seq'.
  apply/negP.
  by apply/negP.
Qed.

Lemma proj_upd d k p w : upd p w k |P| d = upd p w (k |P| d).
Proof.
case/boolP : (p \in d) => X.
by apply proj_upd_in.
by apply proj_upd_notin.
Qed.

Lemma get_proj : forall d k n, n \in d -> get n (k |P| d) = get n k.
Proof.
move=> d [k Hk] n H.
rewrite /get /proj /=.
by apply get_seq_proj_seq.
Qed.

Lemma get_proj_None : forall d k n, n \notin d -> get n (k |P| d) = None.
Proof.
move=> d [k Hk] n H.
rewrite /get /proj /=.
by apply get_seq_proj_seq_None.
Qed.

Lemma disj_proj_emp : forall h1 h2, h1 # h2 -> h1 |P| dom h2 = emp.
Proof.
move=> [l1 H1] [l2 H2].
rewrite /disj /dom /proj /emp /= => H.
apply mk_t_pi => /=.
by apply dis_proj_seq.
Qed.

Lemma disj_proj_same_dom : forall k1 k2 d1 d2, dom k1 = dom k2 ->
  k1 |P| d1 # k1 |P| d2 ->
  k2 |P| d1 # k2 |P| d2.
Proof.
move=> [k1 Hk1] [k2 Hk2] /= d1 d2.
rewrite /dom /proj /= /disj /= /= => Hdom.
by rewrite /proj_seq /= !unzip1_filter Hdom.
Qed.

Lemma dis_disj_proj : forall k1 k2 d1 d2, dis d1 d2 -> k1 |P| d1 # k2 |P| d2.
Proof.
move=> [k1 Hk1] [k2 Hk2] d1 d2 /= H.
rewrite /proj /= /disj /= /proj_seq /= !unzip1_filter.
apply dis_filter_split.
move=> b; split; move/inP=> Hb.
move/disP : H.
move/(_ b) => H.
apply/inP; tauto.
move/disP : H.
move/(_ b) => H.
apply/inP; tauto.
Qed.

Lemma disj_proj_L : forall h d k, h # k -> h |P| d # k.
Proof.
move=> [h1 Hh1] d [k Hk].
rewrite /disj /unzip1 /= /proj_seq => h_d_k.
rewrite /unzip1 -filter_map. by apply dis_filter.
Qed.

Lemma dom_dom_proj : forall h1 h2 d, dom h1 = dom h2 -> dom (h1 |P| d) = dom (h2 |P| d).
Proof.
move=> [h1 H1] [h2 H2] d.
rewrite /dom /proj /proj_seq /unzip1 /= => dom12.
by rewrite -!filter_map dom12.
Qed.

(* NB: move? *)
Lemma filter_app_seq2 : forall (k : seq (l * v)) (Hk : ordered X.ltA (unzip1 k))
  (r p q : pred l),
  (forall b, r b <-> p b \/ q b) ->
  filter (fun x : l * v => r x.1) k =
  app_seq (filter (fun x : l * v => p x.1) k) (filter (fun x : l * v => q x.1) k).
Proof.
elim => //.
case=> h1 h2 t IH /=.
case/ordered_inv=> Hord1 Hord2 r p q Hrpq.
case/boolP : (r h1) => X.
- case: (proj1 (Hrpq _) X) => Y.
  + rewrite Y.
    case/boolP : (q h1) => Z.
    * rewrite /= -(add_seq_is_cons (filter (fun x => q x.1) t) h1 h2); last by apply lb_dom_filter.
      rewrite add_seq_app_seq app_seq_add_seq_add_seq add_seq_is_cons; last first.
        apply lb_unzip1_app_seq; by apply lb_dom_filter.
      f_equal.
      by apply IH.
    * rewrite -(add_seq_is_cons (filter (fun x => p x.1) t) h1 h2); last by apply lb_dom_filter.
      rewrite -add_seq_app_seq add_seq_is_cons; last first.
        apply lb_unzip1_app_seq; by apply lb_dom_filter.
      f_equal.
      by apply IH.
  + rewrite Y.
    case/boolP : (p h1) => Z.
    * rewrite -(add_seq_is_cons (filter (fun x => q x.1) t) h1 h2); last by apply lb_dom_filter.
      rewrite -(add_seq_is_cons (filter (fun x => p x.1) t) h1 h2); last by apply lb_dom_filter.
      rewrite app_seq_add_seq_add_seq add_seq_is_cons; last first.
        apply lb_unzip1_app_seq; by apply lb_dom_filter.
      f_equal.
      by apply IH.
    * rewrite -(add_seq_is_cons (filter (fun x : l * v => q x.1) t) h1 h2); last first.
        by apply lb_dom_filter.
      rewrite -add_seq_app_seq2; last by rewrite unzip1_filter mem_filter negb_and Z.
      rewrite add_seq_is_cons; last by apply lb_unzip1_app_seq; apply lb_dom_filter.
      f_equal.
      by apply IH.
- have [X1 X2] : ~~ p h1 /\ ~~ q h1.
    apply/andP.
    rewrite -negb_or.
    move: X; apply contra => X.
    apply (proj2 (Hrpq _)).
    by apply/orP.
  rewrite (negbTE X1) (negbTE X2); by apply IH.
Qed.

Lemma proj_seq_itself : forall k1, proj_seq k1 (unzip1 k1) = k1.
Proof.
elim=> // hd tl IH /=.
set t := _ \in _.
have -> : t = true by rewrite /t /dom /= in_cons eqxx.
f_equal.
rewrite /proj_seq.
apply trans_eq with (filter predT tl).
- apply: eq_in_filter => x Hx.
  rewrite /dom /= in_cons.
  have -> : (x.1 \in map (fun x => fst x) tl) = true.
  apply/mapP; by exists x.
  by rewrite orbC.
- by apply: filter_predT.
Qed.

Lemma proj_itself : forall k, k |P| dom k = k.
Proof.
move=> [k Hk]; rewrite /proj /dom /=; by apply mk_t_pi, proj_seq_itself.
Qed.

Lemma proj_seq_union_L : forall k1, ordered X.ltA (unzip1 k1) ->
  forall k2, ordered X.ltA (unzip1 k2) ->
  dis (unzip1 k1) (unzip1 k2) ->
  proj_seq (app_seq k1 k2) (map (fun x => fst x) k1) = k1.
Proof.
move=> k1 Hk1 k2. move: k2 k1 Hk1. elim.
- move=> k1 Hord_k1 _ _.
  rewrite app_seq_nil //. by apply proj_seq_itself.
- move=> [h21 h22] t2 IHk2 /= k1 Hord_k1.
  case/ordered_inv => Hord_t2 Hltb_h2 k1_d_k2.
  rewrite /proj_seq filter_app_seq //=; last by constructor.
  set c := _ h21.
  have -> : c = false.
    move: k1_d_k2.
    rewrite dis_sym /=.
    by case: ifP.
  rewrite (filter_dis t2 k1) //; last first.
    move: k1_d_k2.
    rewrite dis_sym /=.
    by case: ifP.
  rewrite app_seq_nil; last first.
    rewrite unzip1_filter. by apply ordered_filter.
  apply trans_eq with (filter predT k1); last by apply filter_predT.
  apply: eq_in_filter => x Hx /=. apply/mapP. by exists x.
Qed.

Lemma proj_union_L : forall (h1 h2 : t) d,
  dis (dom h2) d -> (h1 \U h2) |P| d = h1 |P| d.
Proof.
move=> [h1 H1] [h2 H2] d.
rewrite /dom /= /proj /= => Hdis.
apply mk_t_pi.
rewrite /proj_seq filter_app_seq //.
set d2 := filter _ h2.
suff : d2 = [::].
  move=> ->.
  rewrite app_seq_nil //; exact/ordered_unzip1_filter.
rewrite {}/d2.
transitivity (filter pred0 h2); last by rewrite filter_pred0.
apply eq_in_filter; case=> i1 i2 i_h2 /=.
move/mem_unzip1 : (i_h2) => tmp.
move: (dis_not_in tmp Hdis) => i1_d.
exact/negbTE.
Qed.

Lemma proj_union_L_dom h h1 h2 : h # h2 -> (h1 \U h2) |P| dom h = h1 |P| dom h.
Proof. move=> hh2; apply proj_union_L; rewrite -disjE; exact/disj_sym. Qed.

Lemma proj_union_R_dom : forall h h1 h2, h # h1 -> (h1 \U h2) |P| dom h = h2 |P| dom h.
Proof.
move=> [h H] [h1 H1] [h2 H2] h_d_h1.
rewrite /proj /dom /=.
apply mk_t_pi.
rewrite /proj_seq filter_app_seq //.
set f1 := (filter _ h1).
suff -> : f1 = nil by done.
rewrite /f1.
apply filter_dis.
by rewrite disjE /dom /= dis_sym in h_d_h1.
Qed.

Lemma proj_app : forall k d1 d2, k |P| d1 ++ d2 = (k |P| d1) \U (k |P| d2).
Proof.
move=> [k Hk] d1 d2; rewrite /proj /union /=.
apply mk_t_pi. rewrite /proj_seq.
apply (filter_app_seq2 _ Hk) => b; split=> [Hb|].
apply/orP. by rewrite -mem_cat.
move/orP. by rewrite -mem_cat.
Qed.

Lemma proj_union_sing : forall k x y d, x \in d ->
  (sing x y \U k) |P| d = sing x y \U (k |P| d).
Proof.
move=> [k Hk] x y d x_in_d. rewrite /proj /union /sing /=.
apply mk_t_pi. by rewrite /proj_seq filter_add_seq.
Qed.

Lemma proj_union_sing_notin : forall k x y d, x \notin d ->
  (sing x y \U k) |P| d = k |P| d.
Proof.
move=> [k Hk] x y d Hx. rewrite /proj /union /sing /=.
apply mk_t_pi. rewrite /proj_seq filter_add_seq' //. by apply negbTE.
Qed.

Lemma proj_dom_union : forall h h1 h2, h1 # h2 ->
  h |P| (dom (h1 \U h2)) = (h |P| dom h1) \U (h |P| dom h2).
Proof.
move=> [h Hh] [h1 Hh1] [h2 Hh2] /= h1_d_h2.
rewrite /dom /= /union /= /proj /=.
apply mk_t_pi.
rewrite /proj_seq.
apply (filter_app_seq2 _ Hh) => b; split=> Hb.
  by apply in_map_app_seq_inv.
case: Hb => Hb.
apply in_unzip1_app_seq; by left.
apply in_unzip1_app_seq; by right.
Qed.

Lemma proj_difs : forall k d, k = (k |P| d) \U (k \D\ d).
Proof.
move=> [k Hk] d. rewrite /proj /union /=.
apply mk_t_pi. rewrite /proj_seq /del_seq.
rewrite -(filter_app_seq2 _ Hk predT _ (fun x => x \notin d)).
by rewrite filter_predT.
move=> b; split=> [Hb | //]. apply/orP. by rewrite orbN.
Qed.

Lemma proj_difs_disj : forall k d d', inc d d' -> k |P| d # k \D\ d'.
Proof.
move=> [k Hk] d d'.
rewrite /disj /= => H; apply/disP => x; split.
- rewrite /unzip1 /proj_seq /del_seq /=.
  move/inP. case/mapP. move => [x'1 x'2].
  rewrite mem_filter /=.
  case/andP => Hx1 Hx2 Htmp; subst x'1.
  move/inP. case/mapP. move => [x''1 x''2].
  rewrite mem_filter /=.
  case/andP => Hx'1 Hx'2 Htmp; subst x''1.
  move/incP' in H. move/H : Hx1; exact/negP.
- rewrite /unzip1 /proj_seq /del_seq /=.
  move/inP. case/mapP.  move=> [x'1 x'2].
  rewrite mem_filter /=.
  case/andP => Hx1 Hx2 Htmp; subst x'1.
  move/inP; case/mapP. move=> [x''1 x''2].
  rewrite mem_filter /=.
  case/andP => Hx'1 Hx'2 Htmp; subst x''1.
  move/incP' : H => H; move: Hx'1; move/H; exact/negP.
Qed.

Lemma proj_disj : forall k1 k2 k d, dom k1 = dom k2 -> k1 |P| k # d -> k2 |P| k # d.
Proof.
move=> [k1 H1] [k2 H2] k d.
rewrite /dom /= /unzip1 => dom_k1_k2.
rewrite !disjE /dom /= /proj_seq /unzip1 /= => k1_k_d.
by rewrite -filter_map -dom_k1_k2 filter_map.
Qed.

Definition continuous (A : Type) (def : A) (l : seq A) (ltA : A -> A -> bool) :=
  (forall i,
    0 <= i < size l ->
    ~ exists a, ltA (nth def l i) a /\ ltA a (nth def l i.+1))%nat.

(* TODO: move near the definition of ordered *)
Lemma map_filter_drop : forall k : seq (l * v), ordered X.ltA (unzip1 k) ->
  forall l1 l2, unzip1 k = l1 ++ l2 ->
    filter (fun x => x.1 \in l2) k = drop (size l1) k.
Proof.
move=> k Hk l1.
move Hn1 : (size l1) => n1.
move: n1 k Hk l1 Hn1.
elim.
- move=> /= k Hord [|] // _ l2 /= Hl2.
  rewrite drop0.
  transitivity (filter predT k); last by rewrite filter_predT.
  apply: eq_in_filter => x Hx.
  case: x Hx => x1 x2 Hx /=.
  rewrite -Hl2.
  apply/mapP. by exists (x1, x2).
- move=> n1 IH1 k Hord [|h1 t1] // [Hl1] l2 Hk.
  case: k Hord Hk => [|hk tk] Hord Hk //.
  rewrite /= in Hk.
  case: Hk => ? Hk; subst h1.
  rewrite /= in Hord.
  case/ordered_inv : Hord => Hord1 Hord2.
  move: {IH1}(IH1 _ Hord1 _ Hl1 _ Hk) => IH1 /=.
  case: ifP  => X //.
  have Htmp2 : hk.1 \in unzip1 tk by rewrite Hk mem_cat X orbC.
  move: (mem_lt_lb _ _ _ Hord2 _ Htmp2).
  by rewrite X.ltA_irr.
Qed.

Lemma cdom_proj_R : forall h l1 l2, dom h = l1 ++ l2 ->
  cdom (h |P| l2) = drop (size l1) (cdom h).
Proof.
case=> [k Hk] l1 l2.
rewrite /dom /= => Hdom.
by rewrite /cdom /= /proj_seq (map_filter_drop _ Hk l1) // /unzip2 map_drop.
Qed.

Lemma cdom_difs : forall h l1 l2, dom h = l1 ++ l2 -> cdom (h \D\ l2) = take (size l1) (cdom h).
Proof.
case=> h Hh.
rewrite /dom /cdom  /= => l1 l2 Hdom.
by rewrite /del_seq /unzip2 (map_filter_take X.ltA_irr _ _ Hh l1) // map_take.
Qed.

Lemma app_proj_difs : forall h l1 l2, dom h = l1 ++ l2 -> h |P| l1 = h \D\ l2.
Proof.
move=> [h Hh] l1 l2.
rewrite /dom /proj /difs /= /proj_seq /del_seq /= => dom_h.
apply mk_t_pi.
apply eq_in_filter; move=> [x1 x2] /= Hx.
case/boolP : (x1 \in l1) => Hx1.
- symmetry.
  apply/negP => abs.
  rewrite dom_h in Hh.
  move/ordered_app_inv_ltA : Hh.
  move/(_ _ _ Hx1 abs).
  by rewrite X.ltA_irr.
- apply negbRL.
  apply (map_f (fun x : l * v => fst x)) in Hx.
  rewrite /unzip1 in dom_h.
  rewrite dom_h /= mem_cat in Hx.
  case/orP : Hx => Hx //.
  by rewrite Hx in Hx1.
Qed.

Lemma app_proj_difs2 : forall h l1 l2, dom h = l2 ++ l1 -> h |P| l1 = h \D\ l2.
Proof.
move=> [h Hh] l1 l2.
rewrite /dom /proj /difs /= /proj_seq /del_seq /= => dom_h.
apply mk_t_pi.
apply eq_in_filter; move=> [x1 x2] /= Hx.
case/boolP : (x1 \in l1) => Hx1.
- symmetry.
  apply/negP => abs.
  rewrite dom_h in Hh.
  move/ordered_app_inv_ltA : Hh.
  move/(_ _ _ abs Hx1).
  by rewrite X.ltA_irr.
- apply negbRL.
  apply (map_f (fun x : l * v => fst x)) in Hx.
  rewrite /unzip1 in dom_h.
  rewrite dom_h /= mem_cat in Hx.
  case/orP : Hx => Hx //.
  by rewrite Hx in Hx1.
Qed.

Lemma cdom_proj_L : forall h l1 l2, dom h = l1 ++ l2 ->
  cdom (h |P| l1) = take (size l1) (cdom h).
Proof.
move=> h l1 l2 dom_h.
have -> : h |P| l1 = h \D\ l2 by apply app_proj_difs.
by apply cdom_difs.
Qed.

(** map inclusion *)

Definition inclu h1 h2 := h2 |P| dom h1 = h1.
Local Notation "k '\I' m" := (inclu k m).

Lemma incluE : forall h k, k \I h <-> h |P| dom k = k.
Proof. done. Qed.

Lemma inclu_trans : forall h1 h2 h3, h1 \I h2 -> h2 \I h3 -> h1 \I h3.
Proof.
move=> [h1 H1] [h2 H2] [h3 H3].
rewrite !incluE /proj /dom /=.
case=> K1 []K2.
apply mk_t_pi.
rewrite /proj_seq in K2.
rewrite -{2}K1 /proj_seq -K2 -filter_predI.
apply eq_in_filter => x x_h3 /=.
move Hy : (_ \in _) => y.
destruct y => //=; symmetry.
rewrite -K1 /proj_seq /unzip1 in Hy.
case/mapP : Hy => y Hy x_y.
apply/mapP; exists y => //.
rewrite mem_filter in Hy.
by case/andP : Hy.
Qed.

Lemma inc_seq_inclu' : forall (h1 : seq (l * v))
  (Hh1 : ordered X.ltA (unzip1 h1))
  (h2 : seq (l * v))
  (Hh2 : ordered X.ltA (unzip1 h2))
  (Hincl : forall (n : l) (w : v), get_seq n h1 = Some w -> get_seq n h2 = Some w),
  proj_seq h2 (unzip1 h1) = h1.
Proof.
move=> h1 Hh1 h2.
move: h2 h1 Hh1.
elim.
- move=> h1 Hh1 _ H.
  have X : h1 = [::].
    destruct h1 => //.
    destruct p as [s1 s2].
    move: (H s1 s2).
    rewrite get_seq_cons.
    by move/(_ Logic.eq_refl).
  by rewrite X /=.
- move=> [hd2 hd2'] tl2 IH h1 Hh1.
  rewrite {1}/unzip1 /=.
  case/ordered_inv=> Htl2 Hhd2 Hext.
  case: ifP => X.
  + destruct h1 as [|[hd1 hd1'] tl1].
    * by rewrite /= in X.
    * rewrite /= in_cons in X.
      case/orP : X => X.
      - move/eqP : X => X; subst hd2.
        + have X : hd1' = hd2'.
            move: (Hext hd1 hd1').
            rewrite 2!get_seq_cons.
            move/(_ (refl_equal _)).
            by case.
          subst hd2'.
          f_equal.
          rewrite /= proj_seq_cons; last by apply (mem_lb X.ltA_irr).
          apply IH => //.
          * by case/ordered_inv : Hh1 => //.
          * move=> n w n_w.
            move: (Hext n w).
            have hd1_n : hd1 <> n.
              rewrite /unzip1 /= in Hh1.
              case/ordered_inv : Hh1 => Hhd1 Htl1.
              apply (mem_lb X.ltA_irr) in Htl1.
              apply get_seq_Some_in_unzip1 in n_w.
              move=> ?; subst hd1.
              by rewrite n_w in Htl1.
            rewrite get_seq_cons'; last by auto.
            rewrite get_seq_cons'; by auto.
        + have Z : X.ltA hd1 hd2.
            rewrite /= in Hh1.
            case/ordered_inv : Hh1 => Hhd1 Htl1.
            by apply mem_lt_lb with l (unzip1 tl1). (*NB: I have to explicitly pass the type *)
          have Zabsurd : hd1 = hd2 \/ X.ltA hd2 hd1.
            have Y : hd1 \in (unzip1 (cons (hd2, hd2') tl2)).
              apply get_seq_Some_in_unzip1 with hd1'.
              apply Hext.
              by rewrite get_seq_cons.
            rewrite /= in_cons in Y.
            case/orP : Y => [|Y].
            * move/eqP=> ?; by left.
            * right.
              by apply (mem_lt_lb X.ltA (unzip1 tl2)).
         case: Zabsurd => [Zabsurd|].
          * subst hd2; by rewrite X.ltA_irr in Z.
          * move/(X.ltA_trans Z); by rewrite X.ltA_irr.
  + apply IH => //.
    move=> n w H.
    move: (Hext _ _ H) => H'.
    move: (get_seq_Some_in_unzip1 _ _ _ H) => H''.
    have Y : hd2 <> n by move=> H'''; subst n; rewrite H'' in X.
    by rewrite get_seq_cons' in H'.
Qed.

Lemma get_inclu : forall h1 h2,
  (forall n w, get n h1 = Some w -> get n h2 = Some w) -> h1 \I h2.
Proof.
move=> [h1 Hh1] [h2 Hh2] /= H_h1_h2.
apply mk_t_pi => /=.
rewrite /dom /=.
by apply inc_seq_inclu'.
Qed.

Lemma inclu_get : forall h1 h2, h1 \I h2 ->
  forall n w, get n h1 = Some w -> get n h2 = Some w.
Proof.
move=> [h1 Hh1] [h2 Hh2].
rewrite /inclu /dom /proj /get /=.
case.
move=> Hproj.
move=> n w Hnw.
rewrite -Hproj in Hnw.
case/boolP : (n \in unzip1 h1) => X.
by rewrite get_seq_proj_seq in Hnw.
by rewrite get_seq_proj_seq_None in Hnw.
Qed.

Lemma inclu_inc : forall h1 h2, h1 \I h2 -> inc (elts h1) (elts h2).
Proof.
move=> [h1 Hh1] [h2 Hh2].
rewrite /inclu /dom /proj /get /=.
case.
move=> Hproj.
apply/incP' => x Hx.
apply in_proj_seq_inv with (unzip1 h1).
by rewrite Hproj.
Qed.

Lemma inclu_inc_dom : forall h1 h2, h1 \I h2 -> inc (dom h1) (dom h2).
Proof.
move=> [h1 Hh1] [h2 Hh2].
move/inclu_inc => /= H1.
rewrite /dom /=.
by apply inc_map_fst.
Qed.

Lemma inclu_union_L : forall h1 h2 k, h1 # h2 -> k \I h1 -> k \I (h1 \Uh2).
Proof.
move=> [h1 Hh1] [h2 Hh2] [k Hk] h1_d_h2.
rewrite /inclu /proj /proj_seq /dom /=.
case => k_h1.
apply mk_t_pi.
rewrite filter_app_seq // k_h1.
rewrite (_ : filter _ _ = filter pred0 h2); last first.
  apply: eq_in_filter.
  case=> x1 x2 xh2.
  apply/negP => abs'.
  move/disP : h1_d_h2.
  move/(_ x1) => /= [] _.
  apply.
  apply/inP.
  rewrite /= in abs'.
  apply/mapP; by exists (x1, x2).
  move/inP : abs'.
  rewrite /unzip1 /= => H.
  rewrite -k_h1 in H.
  move/inP : H.
  case/mapP => y Hy ?; subst x1.
  rewrite mem_filter in Hy.
  case/andP : Hy => _ Hy.
  apply/inP.
  apply/mapP. destruct y as [y1 y2]. by exists (y1, y2).
by rewrite filter_pred0 app_seq_nil.
Qed.

Lemma inclu_union_R  h1 h2 k : h1 # h2 -> k \I h2 -> k \I (h1 \U h2).
Proof.
move=> h1dh2 kh2.
rewrite unionC //.
apply inclu_union_L => //.
by apply disj_sym.
Qed.

Lemma inclu_refl k : k \I k.
Proof. by rewrite /inclu proj_itself. Qed.

Lemma proj_inclu : forall k h1 d, k \I (h1 |P| d) -> k \I h1.
Proof.
move=> [k Hk] [h1 Hh1] d H0.
rewrite /inclu /proj.
apply: mk_t_pi => /=.
rewrite /inclu /proj /= in H0.
case: H0 => H0.
rewrite -{2}H0 /proj_seq -filter_predI.
apply: eq_in_filter.
case=> x1 x2 xh1 /=.
case/boolP : (x1 \in d) => x1d.
  by rewrite andbC.
rewrite andbC /=.
apply/negP => abs.
rewrite {1}/proj_seq in H0.
rewrite /dom /= -H0 in abs.
case/mapP : abs => /= [x1' x2'] H1.
subst x1.
rewrite mem_filter in x2'.
case/andP : x2' => H2 H3.
rewrite /proj_seq mem_filter in H3.
case/andP : H3 => H3 H4.
by rewrite H3 in x1d.
Qed.

Definition del_elt n k := del_seq [::n] k.

Lemma in_unzip1_del_elt : forall l0 x h1, x <> h1 ->
  x \in unzip1 l0 -> x \in unzip1 (del_elt h1 l0).
Proof.
elim=> //; case=> [h1 h2] tl IH x h0 x_h0 /=.
rewrite /unzip1 /= in_cons /=.
case/orP => X.
move/eqP : X => ?; subst h1.
rewrite in_cons negb_or.
move/eqP : x_h0 => x_h0.
by rewrite x_h0 /= in_cons eqxx /=.
rewrite in_cons negb_or /= andbC /=.
case: ifP => Y.
by rewrite /= in_cons IH // orbC.
by apply IH.
Qed.

Lemma unzip1_add_seq_del_elt : forall l0 h1 h2,
  ordered X.ltA (unzip1 l0) ->
  h1 \in unzip1 l0 ->
  unzip1 l0 = unzip1 (add_seq h1 h2 (del_elt h1 l0)).
Proof.
elim=> //; case=> h1 h2 tl IH h3 h4.
rewrite /=.
case/ordered_inv => H1 H2.
rewrite !in_cons /= !in_nil /= negb_or andbC /=.
case/orP.
- move/eqP=> ?; subst h3.
  rewrite eqxx /= add_seq_is_cons /=; last first.
  rewrite /del_elt /del_seq; by apply lb_dom_filter.
  f_equal.
  rewrite /del_elt del_seq_invariant // dis_sym /=.
  apply (mem_lb X.ltA_irr) in H2; by rewrite (negbTE H2).
- move=> h3_tl.
  case: ifP => Y.
  + rewrite -add_seq_is_cons; last by apply lb_dom_filter.
    rewrite add_seq_add_seq_neq; last by by apply/eqP.
    rewrite add_seq_is_cons; last first.
      apply lb_add_seq.
      by apply lb_dom_filter.
      by apply (mem_lt_lb X.ltA (unzip1 tl) h1).
    by rewrite /= -IH.
  + move/eqP : Y => ?; subst h3.
    apply (mem_lb X.ltA_irr) in H2.
    by rewrite h3_tl in H2.
Qed.

Lemma not_mem_dom_del_elt : forall k n, ~ n \in unzip1 k -> del_elt n k = k.
Proof.
move=> k n H.
rewrite /del_elt.
apply del_seq_invariant.
rewrite dis_sym /=.
by case:ifP.
Qed.

Lemma mem_dom_del_elt' : forall k n, n \in unzip1 (del_elt n k) = false.
Proof.
elim=> //=.
move=> [h1 h2] /= tl IH n.
case/boolP : (h1 == n) => X.
- by rewrite !in_cons X IH.
- move/negbTE : X => X.
  by rewrite !in_cons X /= !in_cons (IH n) eq_sym X.
Qed.

Lemma del_seq_del_elt : forall k n ns, del_seq (n :: ns) k = del_seq ns (del_elt n k).
Proof.
elim=> //=.
move=> [h1 h2] /= tl IH n ns.
rewrite !in_cons; rewrite negb_or.
case/boolP : (n == h1) => X.
- move/eqP:X=>X; subst.
  rewrite eq_refl /=.
  by apply IH.
- move/negbTE : X => X.
  rewrite eq_sym X /=.
  have [Y|Y] : h1 \in ns \/ h1 \in ns = false by case (h1 \in ns); auto.
  rewrite Y /=.
  apply IH.
  by rewrite Y /= IH.
Qed.

Lemma unzip1_app_seq_del_seq : forall k l,
  ordered X.ltA (unzip1 l) -> ordered X.ltA (unzip1 k) ->
  inc (unzip1 k) (unzip1 l) ->
  unzip1 l = unzip1 (app_seq k (del_seq (unzip1 k) l)).
Proof.
elim=> //=.
- move=> l0 Hl0 Hk Hi /=.
  rewrite /del_seq.
  f_equal.
  apply trans_eq with (filter predT l0).
  rewrite filter_predT //.
  by apply: eq_in_filter.
- move=> [h1 h2] /= tl IH l0 Hl0 Hk Hi.
  rewrite del_seq_del_elt.
  case/ordered_inv : Hk => Hk1 Hk2.
  move: Hi.
  case: ifP => // X Hi.
  rewrite add_seq_app_seq2; last by apply (mem_lb X.ltA_irr) in Hk2.
  rewrite /del_seq.
  rewrite -(filter_add_seq (del_elt h1 l0) _ _ _ (fun x => x \notin unzip1 tl)) //; last 2 first.
    by apply ordered_del_seq.
    by apply (mem_lb X.ltA_irr) in Hk2.
  rewrite -IH //; last 2 first.
    by apply ordered_add_seq, ordered_del_seq.
    apply/incP' => x Hx.
    apply in_unzip1_add_seq_remains.
    apply in_unzip1_del_elt => //.
      move=> ?; subst h1.
      apply (mem_lb X.ltA_irr) in Hk2.
      by rewrite Hx in Hk2.
    move/incP' : Hi; by apply.
  by apply unzip1_add_seq_del_elt.
Qed.

Lemma add_seq_del_elt'' : forall (k : seq (X.A * E.A)) n w,
  ordered X.ltA (unzip1 k) -> (n, w) \in k ->
  k = add_seq n w (del_elt n k).
Proof.
elim=> //=.
move=> [hd1 hd2] /= tl IH n w.
case/ordered_inv => H1 H2.
rewrite !in_cons; case/orP.
- case/eqP=> X Y; subst.
  rewrite eq_refl /=.
  move: (mem_lb X.ltA_irr H2) => H2'.
  rewrite not_mem_dom_del_elt; last first.
    apply/negP; by rewrite H2'.
  by rewrite /add_seq /= (negbTE H2') /= add_map_is_cons.
- move=> X.
  have Y : X.ltA hd1 n.
    apply (mem_lt_lb X.ltA _ _ H2). apply mem_unzip1 with w. by apply X.
  rewrite (lt_neq X.ltA_total Y) /= /add_seq /=.
  rewrite eq_sym (lt_neq X.ltA_total Y) /=.
  rewrite !in_cons /= mem_dom_del_elt'.
  rewrite eq_sym (lt_neq X.ltA_total Y) /=.
  rewrite (flip X.ltA_trans X.ltA_irr Y) /=.
  move: (IH _ _ H1 X) => IH'.
  rewrite /add_seq mem_dom_del_elt' in IH'.
  by rewrite -IH'.
Qed.

Lemma ordered_del_elt : forall k, ordered X.ltA (unzip1 k) -> forall n, ordered X.ltA (unzip1 (del_elt n k)).
Proof. move=> k H n. rewrite /del_elt. by apply ordered_del_seq. Qed.

Lemma app_seq_del_seq : forall k l,
  ordered X.ltA (unzip1 l) -> ordered X.ltA (unzip1 k) ->
  inc k l -> l = app_seq k (del_seq (unzip1 k) l).
Proof.
elim=> //=.
- move=> l0 Hl0 Hk Hi /=.
  rewrite /del_seq.
  apply trans_eq with (filter predT l0).
  rewrite filter_predT //.
  by apply: eq_in_filter.
- move=> [h1 h2] /= tl IH l0 Hl0 Hk Hi.
  rewrite del_seq_del_elt -IH.
  + apply add_seq_del_elt'' => //.
    move: Hi.
    by case: ifP.
  + by apply ordered_del_elt.
  + by case/ordered_inv : Hk.
  + apply inc_trans with (filter (fun x : prod_eqType l v => ~~ (x.1 \in [:: h1])) tl).
    * have H : filter (fun x => ~~ (x.1 \in [:: h1])) tl = filter predT tl.
        apply: eq_in_filter => x H /=.
        rewrite negb_or /= andbC /=.
        case/ordered_inv : Hk => Hk1 Hk2.
        apply/eqP => X; subst.
        move/(mem_lb X.ltA_irr) : Hk2.
        move/negP.
        by move/not_unzip1_not_mem.
      by rewrite H filter_predT inc_refl.
    * rewrite /del_elt /del_seq.
      apply inc_filter; by case: ifP Hi.
Qed.

Lemma filter_app_seq' : forall k (Hk : ordered X.ltA (unzip1 k)) p,
  k = app_seq (filter (fun x => p (fst x)) k) (filter (fun x => ~~ p (fst x)) k).
Proof.
elim => //.
case=> h11 h12 tl IH /=.
case/ordered_inv => H1 H2 p.
case: ifP => X /=.
- by rewrite add_seq_is_cons -IH.
- move: {IH}(IH H1 (fun x => p x)) => IH.
  rewrite app_seq_com /=; last 3 first.
    rewrite unzip1_filter; by apply ordered_filter.
    constructor.
    rewrite (unzip1_filter _ (fun x => ~~ p x)); by apply ordered_filter.
    rewrite (unzip1_filter _ (fun x => ~~ p x)); by apply lb_incl.
    rewrite dis_sym /=.
    case: ifP.
      case/mapP => /= x.
      rewrite mem_filter => /andP [] abs _.
      by rewrite -X => ->.
    move=> H.
    rewrite unzip1_filter unzip1_filter' dis_sym.
    apply: dis_filter_split.
    by move=> b; split => // Hb; apply/negPn.
  rewrite {1}IH app_seq_com; last 3 first.
    rewrite unzip1_filter; by apply ordered_filter.
    rewrite (unzip1_filter _ (fun x => ~~ p x)); by apply ordered_filter.
    rewrite unzip1_filter unzip1_filter'.
    apply: dis_filter_split.
    by move=> b; split => // Hb; apply/negPn.
  rewrite /= add_seq_is_cons // app_seq_com; last 3 first.
    rewrite (unzip1_filter _ (fun x => ~~ p x)); by apply ordered_filter.
    rewrite unzip1_filter; by apply ordered_filter.
    rewrite unzip1_filter unzip1_filter' dis_sym. 
    apply: dis_filter_split.
    by move=> b; split => // Hb; apply/negPn.
  by rewrite -IH.
Qed.

Lemma app_seq_del_seq_proj_seq : forall k d,
  ordered X.ltA (unzip1 k) -> k = app_seq (del_seq d k) (proj_seq k d).
Proof.
move=> k d Hk.
rewrite /del_seq /proj_seq.
rewrite app_seq_com.
apply filter_app_seq' => //.
rewrite unzip1_filter'; by apply ordered_filter.
rewrite unzip1_filter; by apply ordered_filter.
rewrite dis_sym unzip1_filter unzip1_filter'.
apply dis_filter_split.
by move=> b; split => // Hb; apply/negPn.
Qed.

Lemma proj_seq_restrict' : forall (h2 : seq (l * v))
  (Hh2 : ordered X.ltA (unzip1 h2)) (d d' : seq l),
  inc d d' -> proj_seq h2 d = proj_seq (proj_seq h2 d') d.
Proof.
elim=> //; case=> [h2 h2'] t2 IH /=.
case/ordered_inv => Hh2 Ht2 d d' Hincl.
case/boolP : (h2 \in d) => [h2_d|X].
- move/incP' in Hincl.
  move: (Hincl _ h2_d) => h2_d'.
  rewrite h2_d' /=.
  rewrite {}h2_d.
  f_equal.
  apply IH => //.
  exact/incP'.
- case/boolP : (h2 \in d') => Y.
  + by rewrite /= (negbTE X) /= -IH.
  + by rewrite -IH.
Qed.

Lemma proj_restrict' : forall d d' h2, inc d d' -> h2 |P| d = (h2 |P| d') |P| d.
Proof.
move=> d d' [h2 Hh2] H.
rewrite /proj /=.
by apply mk_t_pi, proj_seq_restrict'.
Qed.

Lemma proj_restrict h1 h2 d : h1 \I h2 -> inc d (dom h1) -> h2 |P| d = h1 |P| d.
Proof.
move=> H_h1_h2 H_d_h1.
rewrite /inclu in H_h1_h2.
rewrite -H_h1_h2; by apply proj_restrict'.
Qed.

(* TODO: not an interesting generalization? *)
Lemma union_difsK h k d : k \I h -> dom k = d -> h = k \U (h \D\ d).
Proof.
move=> H k_d.
apply equal_eq.
rewrite /equal /= -k_d.
apply app_seq_del_seq => //.
- by destruct h.
- by destruct k.
- by move/inclu_inc : H.
Qed.

Lemma dom_union_difsK : forall h k, inc (dom k) (dom h) -> dom h = dom (k \U (h \D\ dom k)).
Proof.
move=> [h0 H0] [k Hk]. rewrite /dom /= => H; exact: unzip1_app_seq_del_seq.
Qed.

Lemma get_inclu_sing : forall h a b, get a h = Some b -> sing a b \I h.
Proof.
move=> [h0 H0] a b H.
apply get_inclu => n w.
rewrite /get /get_seq /= => H'.
case/boolP : (n == a) => X.
  rewrite X in H'.
  by rewrite (eqP X) -H'.
by rewrite (negbTE X) in H'.
Qed.

Lemma inclu_proj : forall k d, (k |P| d) \I k.
Proof.
move=> [k Hk] d.
apply get_inclu => n w.
rewrite /get /=.
case/boolP : (n \in d) => X.
  by rewrite get_seq_proj_seq.
rewrite notin_get_seq_None //.
move/negP : X => X; contradict X.
apply/inP.
move/incP: (inc_dom_proj d (mk_t k Hk)).
apply.
exact/inP.
Qed.

(* TODO: a remonter? *)
Lemma proj_dom_proj : forall k d, k |P| dom (k |P| d) = k |P| d.
Proof.
move=> [k Hk] d.
rewrite /proj /= /dom /=.
apply mk_t_pi.
apply inc_seq_inclu' => //.
rewrite /proj_seq unzip1_filter.
by apply ordered_filter.
move: (inclu_proj (mk_t k Hk) d).
move/inclu_get => H n w.
case/boolP : (n \in d) => X.
by rewrite get_seq_proj_seq.
by rewrite get_seq_proj_seq_None.
Qed.

(*
NB: this is by definition !
Lemma inclu_proj_dom : forall h k, k [<=m] h -> proj h (dom k) = k.
Proof.
move=> [h Hh] [k Hk].
rewrite /inclu /proj /dom /=.
case => H.
by apply mk_t_pi.
Qed.
*)

Lemma proj_seq_del_seq : forall (k : seq (l * v)) (Hk : ordered X.ltA (unzip1 k)) (d : seq l),
  proj_seq k (unzip1 (del_seq d k)) = del_seq d k.
Proof.
elim=> //.
move=> [hd hd'] tl IH.
rewrite {1}/unzip1 [ordered _ _]/=.
case/ordered_inv => Hhd Htl d.
rewrite /=.
case/boolP : (hd \notin d) => X.
- rewrite /= in_cons eqxx /=.
  f_equal.
  rewrite proj_seq_cons.
  by apply IH.
  by apply (mem_lb X.ltA_irr).
- apply negbNE in X.
  move: (negbTE (notin_unzip1_del_seq _ tl _ X)).
  rewrite /unzip1 => ->.
  by apply IH.
Qed.

Lemma proj_seq_del_seq2 : forall k x d, x \in d ->
  proj_seq (del_seq (cons x [::]) k) d = del_seq (cons x [::]) (proj_seq k d).
Proof.
elim=> //.
case=> hd1 hd2 tl IH x d Hx.
rewrite /=.
rewrite in_cons negb_or in_nil andbC /=.
case/boolP : (hd1 == x) => X.
- move/eqP : X => X; subst hd1.
  rewrite Hx /= in_cons negb_or in_nil eqxx /=.
  by apply IH.
- rewrite /=.
  case: ifP => Y.
  + by rewrite /= in_cons in_nil negb_or X /= IH.
  + by apply IH.
Qed.

Lemma inclu_difs : forall h d, (h \D\ d) \I h.
Proof.
move=> [k Hk] d. rewrite /difs /inclu /proj /dom /=.
apply mk_t_pi. by apply proj_seq_del_seq.
Qed.

Lemma difs_difs s x y : (s \D\ y) \D\ x = (s \D\ x) \D\ y.
Proof.
case: s => [s Hs] /=; apply mk_t_pi; rewrite /del_seq -!filter_predI.
apply eq_filter => z /=; by rewrite andbC.
Qed.

(* NB: the following does not hold:
Lemma inc_dom_inclu' : forall h1 h2, inc (dom h1) (dom h2) -> h1 [<=m] h2.
*)

Lemma disj_proj_inclu : forall h d1 k,
  h |P| d1 # k -> h |P| d1 \I (h \D\ dom k).
Proof.
move=> [k Hk] d1 h /= Hdisj.
apply get_inclu => n w.
rewrite /get /= /proj /= /dom /= /del_seq /= => H.
move: (get_seq_Some_in _ _ _ H) => /= Hnw.
apply ord_in_get_seq_Some.
by apply ordered_unzip1_filter.
rewrite mem_filter /=.
apply/andP; split.
rewrite /proj in Hdisj.
apply/inP.
move/disP : Hdisj => Hdisj.
apply (proj1 (Hdisj _)).
apply/inP.
by move/mem_unzip1 : Hnw.
by apply in_proj_seq_inv with d1.
Qed.

Lemma incl_proj2 : forall h1 h2 k, h1 \I k -> h2 \I k -> dom h1 = dom h2 -> h1 = h2.
Proof.
move=> [h1 H1] [h2 H2] k.
rewrite /inclu /dom /= /proj /proj_seq /=.
case=> h1_k [h2_k dom_h12].
apply mk_t_pi.
rewrite -h1_k -h2_k.
apply: eq_in_filter; move=> [a1 a2] a_k /=.
by rewrite dom_h12.
Qed.

Lemma disj_proj_app : forall h k d1 d2, h # (k \D\ d1) -> h # (k \D\ d2) ->
  h # (k \D\ (d1 ++ d2)).
Proof.
move=> [h0 Hh0] [k Hk] d1 d2.
rewrite /difs /disj /=; move/disP => H1 /disP H2.
apply/disP => x; split => Hx.
- move/(proj1 (H1 _)) : (Hx) => /inP {}H1.
  move/(proj1 (H2 _)) : Hx => /inP {}H2.
  exact/inP/notin_unzip1_del_seq_app.
- move=> Hx'.
  move/(proj1 (H1 _)) : (Hx') => /inP {}H1.
  move/(proj1 (H2 _)) : Hx' => /inP {}H2.
  move: Hx.
  exact/inP/notin_unzip1_del_seq_app.
Qed.

Definition dif h l := h \D\ [:: l].
Local Notation "k '\d\' l" := (dif k l).

Lemma difE : forall h n, h \d\ n = h \D\ [:: n]. by []. Qed.

Lemma size_del_seql l (Hl : ordered X.ltA (unzip1 l)) a :
 get_seq a l != None -> (size (unzip1 (del_seq [:: a] l)) < size (unzip1 l))%nat.
Proof.
elim: l Hl a => // h t IH /=.
case/ordered_inv => H1 H2 a; rewrite /get_seq /=.
case: ifP => [/eqP -> _ | ah1].
  rewrite inE eqxx /=.
  case/boolP : (get_seq h.1 t == None) => [/eqP |] ht.
    rewrite del_seq_invariant // dis_sym dis_cons /=.
    by move/get_seq_None_notin : ht => /negP.
  apply ltn_trans with (size (unzip1 t)) => //; by apply IH.
move K : (ocamlfind _ _) => k.
case: k K => //= A HA _.
by rewrite inE eq_sym ah1 /= ltnS IH // /get_seq HA.
Qed.

Lemma size_dom_dif a h : get a h != None -> (size (dom (h \d\ a)) < size (dom h))%nat.
Proof. case: h a => l Hl a /=; by apply size_del_seql. Qed.

Lemma dif_sing a b : sing a b \d\ a = emp.
Proof. apply equal_eq. by rewrite /sing /dif /equal /= !in_cons eqxx. Qed.

Lemma dif_emp p : emp \d\ p = emp. Proof. by apply extensionality. Qed.

Lemma mem_dom_del_elt : forall k n n', n <> n' -> n \in unzip1 (del_elt n' k) = (n \in unzip1 k).
Proof.
elim=> //=.
move=> [h1 h2] /= tl IH n n' H.
case/boolP : (h1 == n') => X.
- move/eqP:X=>X; subst.
  rewrite !in_cons eq_refl /=.
  have Y : n' == n = false by apply/eqP; auto.
  rewrite eq_sym Y /=.
  by apply IH.
- move/negbTE : X => X.
  by rewrite !in_cons X /= !in_cons IH.
Qed.

Lemma del_elt_upd_seq : forall k n w, del_elt n (upd_seq n w k) = del_elt n k.
Proof.
elim=> //=.
move=> [h1 h2] /= tl IH n w.
case/boolP : (h1 == n) => X.
- move/eqP:X=>X; subst.
  by rewrite eq_refl /= !in_cons eq_refl.
- move/negbTE : X => X.
  by rewrite eq_sym X /= !in_cons X /= IH.
Qed.

Lemma del_elt_upd_seq' : forall k n n' w, n <> n' -> del_elt n (upd_seq n' w k) = upd_seq n' w (del_elt n k).
Proof.
elim=> //=.
move=> [h1 h2] /= tl IH n n' w H.
case/boolP : (n' == h1) => X.
- rewrite /=.
  case/boolP : (h1 == n) => Y.
  + move/eqP:X=>X; subst.
    move/eqP:Y=>Y; subst.
    tauto.
  + move/negbTE : Y => Y.
    by rewrite !in_cons Y /= X.
- move/negbTE : X => X.
  rewrite /=.
  case/boolP : (h1 == n) => Y.
  - rewrite !in_cons Y /=.
    by apply IH.
  - move/negbTE : Y => Y.
    by rewrite !in_cons Y /= X /= IH.
Qed.

Lemma add_seq_del_elt' : forall k n w, del_elt n (add_seq n w k) = del_elt n k.
Proof.
elim=> //=.
- move=> n w.
  by rewrite !in_cons eq_refl.
- move=> [h1 h2] /= tl IH n w.
  rewrite /add_seq /=.
  case/boolP : (h1 == n).
  - move/eqP =>X; subst.
    by rewrite !in_cons eq_refl /= !in_cons eq_refl.
  - move/negbTE => X.
    rewrite !in_cons X /=.
    case/boolP : (n \in unzip1 tl) => [|Y].
    + by rewrite /= eq_sym X /= !in_cons X /= del_elt_upd_seq.
    + rewrite /= eq_sym X /=.
      case: ifP => [|Z].
      * by rewrite /= !in_cons eq_refl /= X.
      * rewrite /= !in_cons X /=.
        move: {IH}(IH n w) => IH.
        rewrite /add_seq /= (negbTE Y) in IH.
        by rewrite IH.
Qed.

Lemma add_seq_del_elt: forall lst n w n', ordered X.ltA (unzip1 lst) ->
  n' <> n -> add_seq n w (del_elt n' lst) = del_elt n' (add_seq n w lst).
Proof.
elim=> //=.
- move=> n w n' _. move/eqP => Hn'n.
  by rewrite negb_or eq_sym Hn'n /add_seq.
- move=> [h1 h2] /= tl IH n w n'.
  case/ordered_inv => H1 H2 H.
  case/boolP : (h1 == n').
  - move/eqP => X; subst.
    by rewrite !in_cons eqxx /= IH // -add_seq_is_cons // add_seq_add_seq_neq // add_seq_del_elt'.
  - move/negbTE => X.
    rewrite !in_cons X /= /add_seq /=.
    case/boolP : (h1 == n) => [Y|].
    + by rewrite !in_cons eq_sym Y /= !in_cons X.
    + move/negbTE => Y.
      rewrite !in_cons mem_dom_del_elt; last by auto.
      case/boolP : (n \in unzip1 tl) => [|Z].
      * by rewrite /= eq_sym Y /= !in_cons /= X /= del_elt_upd_seq'.
      * rewrite /=.
        case/boolP : (X.ltA n h1) => W.
        - move/eqP: H => H.
          by rewrite eq_sym Y /= negb_or eq_sym H /= !in_cons X.
        - rewrite eq_sym Y /= /= !in_cons X /=.
          move: {IH}(IH _ w _ H1 H) => IH.
          rewrite /add_seq mem_dom_del_elt in IH; last by auto.
          rewrite (negbTE Z) in IH.
          by rewrite IH.
Qed.

Lemma get_seq_del_elt : forall w st, get_seq w (del_elt w st) = None.
Proof. move=> w st. apply get_seq_del_seq. by rewrite in_cons in_nil eqxx. Qed.

Lemma get_seq_del_elt' : forall k x y, x <> y -> get_seq x (del_elt y k) = get_seq x k.
Proof. move=> k x y Hxy. apply get_seq_del_seq'. rewrite in_cons negb_or in_nil andbC /=. apply/eqP; auto. Qed.

Lemma del_elt_app_seq : forall k m n, ordered X.ltA (unzip1 m) -> ordered X.ltA (unzip1 k) ->
  del_seq [:: n] (app_seq k m) = app_seq (del_seq [:: n] k) (del_seq [:: n] m).
Proof.
elim=> //=.
move=> [h1 h2] /= tl IH m n H.
case/ordered_inv => H1 H2.
rewrite !in_cons; case/boolP : (h1 == n) => X.
- move/eqP in X; subst.
  rewrite /= -/(del_elt n (add_seq n h2 (app_seq tl m))) add_seq_del_elt' /= /del_elt.
  by apply IH.
- move/negbTE : X => X.
  rewrite /=.
  rewrite -/(del_elt n (add_seq h1 h2 (app_seq tl m))) -add_seq_del_elt //; last 2 first.
    by apply ordered_app_seq.
    by move/eqP:X; auto.
  by rewrite /del_elt IH.
Qed.

Lemma dif_not_in_dom: forall h l, ~ l \in unzip1 (elts h) -> h \d\ l = h.
Proof.
move=> [h1 H1] /= n H.
apply equal_eq.
rewrite /dif /equal /=.
apply del_seq_invariant => //.
rewrite dis_sym /=.
by case: ifP.
Qed.

Lemma dif_union: forall h1 h2 a, (h1 \U h2) \d\ a = (h1 \d\ a) \U (h2 \d\ a).
Proof.
move=> [h1 H1] [h2 H2] a /=.
apply equal_eq.
rewrite /dif /union /equal /=.
by apply del_elt_app_seq.
Qed.

Lemma dif_disj: forall h a b, h # sing a b  ->  h \d\ a = h.
Proof.
move=> [h1 H1] /= a b H.
apply dif_not_in_dom => /=.
rewrite /disj /= dis_sym /= in H.
move: H.
by case: ifP.
Qed.

Lemma dif_disj' : forall h1 h2 l, h1 # h2 -> h1 \d\ l # h2 \d\ l.
Proof.
move=> [h1 H1] [h2 H2] n /=.
rewrite /disj /= => H.
rewrite /del_elt /del_seq.
rewrite (unzip1_filter _ (fun x => ~~ (x \in [::n]))) (unzip1_filter _ (fun x => ~~ (x \in [::n]))).
apply dis_filter => //.
rewrite dis_sym.
apply dis_filter => //.
by rewrite dis_sym.
Qed.

Lemma dis_dif : forall h k, k # h \D\ unzip1 (elts k).
Proof.
move=> [h1 H1] [k K] /=.
rewrite /difs /= /disj /= /del_seq.
rewrite (unzip1_filter _ (fun n => ~~ (n \in unzip1 k))).
by apply dis_filter_right.
Qed.

Lemma get_dif w st : get w (st \d\ w) = None.
Proof. by rewrite /get /dif /= get_seq_del_elt. Qed.

Lemma get_dif' st x y : x <> y -> get x (st \d\ y) = get x st.
Proof. move=> H; by rewrite /get /dif /= get_seq_del_elt'. Qed.

Lemma proj_dif : forall k x d, x \in d -> (k \d\ x) |P| d = (k |P| d) \d\ x.
Proof.
move=> [k Hk] x d Hx.
rewrite /proj /=.
apply mk_t_pi => /=.
by apply proj_seq_del_seq2.
Qed.

End compmap.

(* NB: <: MAP breaks the Disj_heap/Equal_heap tactics *)
Module map (X : ORDER) (E : EQTYPE) : MAP
  with Definition l := X.A
    with Definition v := E.A
      with Definition ltl := X.ltA.

Module m := compmap X E.

Include m.

End map.

(** Additional, derived properties *)

Module Map_Prop (M : MAP).

Import M.
Notation "k '#' m" := (disj k m).
Notation "k '\U' m" := (union k m).
Notation "k '\D\' m" := (difs k m).
Notation "k '|P|' m" := (proj k m).
Notation "k '\I' m" := (inclu k m).
Notation "k '\d\' l" := (dif k l).

Lemma emp_sing_dis a b : M.emp <> M.sing a b.
Proof.
move=> abs.
have abs1 : M.get a (M.sing a b) = Some b by rewrite M.get_sing.
by rewrite -abs M.get_emp in abs1.
Qed.

Lemma get_exists_sing h a b : M.get a h = Some b ->
  exists h', h = M.sing a b \U h' /\ M.sing a b # h'.
Proof.
move=> H; exists (M.dif h a); split.
- rewrite M.difE; apply M.union_difsK;
  by [apply M.get_inclu_sing | rewrite M.dom_sing].
- rewrite M.difE -(M.dom_sing a b); exact/M.disj_difs'/inc_refl.
Qed.

Lemma proj_difs_disj_spec k d : k |P| d # k \D\ d.
Proof. apply proj_difs_disj; by rewrite inc_refl. Qed.

Lemma union_reg h k l : h \U k = h \U l -> k # h -> l # h -> k = l.
Proof.
move=> H1 H2 H3; by case: (M.union_inv _ _ _ _ H1 (erefl _) H2 H3).
Qed.

Lemma swap_heads x rx y ry k : uniq (x :: y :: nil) ->
  M.sing x rx \U (M.sing y ry \U k) = M.sing y ry \U (M.sing x rx \U k).
Proof.
move=> H.
apply M.permut_eq.
rewrite M.unionA.
apply Permutation_sym.
rewrite M.unionA (M.unionC (M.sing y ry)); last first.
  apply M.disj_sing.
  apply/eqP; by Uniq_neq.
by apply Permutation_refl.
Qed.

Lemma inclu_union_inv_L h1 h2 h : h1 # h2 -> (h1 \U h2) \I h -> h1 \I h.
Proof.
move=> h1_d_h2 H.
have -> : h1 = (h1 \U h2) \D\ dom h2.
  rewrite unionC // difs_union_L.
  by rewrite difs_self unioneh.
  by rewrite disjE in h1_d_h2.
apply inclu_trans with (h1 \U h2) => //.
by apply inclu_difs.
Qed.

Lemma inclu_union_inv_R h1 h2 h : h1 # h2 -> (h1 \U h2) \I h -> h2 \I h.
Proof.
move=> h1_d_h2 H.
rewrite unionC // in H.
apply inclu_union_inv_L with h1 => //.
exact/disj_sym.
Qed.

(*
   h'1 +++    h'2
   h2     +++ h1
   ->
   h2 = h'1 +++ h' with h' # h'1
*)

Lemma app_inclu : forall h1 h2 h3 h4, h1 # h2 -> h3 # h4 ->
  h1 # h3 ->
  h1 \U h2 = h3 \U h4 ->
  h3 \I h2.
Proof.
move=> h1 h2 h3 h4 H12 H34 H13 H.
apply M.get_inclu => n w H_n_h3.
have X : get n (h1 \U h2) = Some w by rewrite H; by apply get_union_L.
case: (get_union_Some_inv h1 h2 n w X) => // Y.
move/get_Some_in_dom : H_n_h3 => H_n_h3.
move/get_Some_in_dom : Y => Y.
rewrite disjE in H13.
move/disP : H13 => H13.
case: (H13 n).
move/inP : Y => Y.
move/(_ Y).
by move/inP : H_n_h3.
Qed.

Lemma disj_comp k1 h1 h2 k2 : h1 # k1 -> h1 # h2 -> k1 # k2 ->
  k1 \U k2 = h1 \U h2 ->
  exists h', k1 # h' /\ h2 = h' \U k1.
Proof.
move=> X Y Z W.
exists (k2 \D\ M.dom h1); split.
- by apply M.disj_difs.
- apply (union_reg h1).
  + rewrite -W M.unionC // M.unionA.
    have <- : k2 = h1 \U (k2 \D\ M.dom h1).
      apply M.union_difsK; last by [].
      apply (app_inclu k1 _ _ h2) => //; exact/M.disj_sym.
    rewrite M.unionC //; exact/M.disj_sym.
  + exact/M.disj_sym.
  + apply M.disjUh; last exact/disj_sym.
    by apply disj_sym, (M.disj_difs' h1 k2), inc_refl.
Qed.

Fixpoint mk_finmap (lst : seq (l * v)) : t :=
  if lst is (hd1, hd2) :: tl then sing hd1 hd2 \U mk_finmap tl else emp.

Lemma elts_mk_finmap : forall l, ordset.OrderedSequence.ordered M.ltl (unzip1 l) ->
  elts (mk_finmap l) = l.
Proof.
elim => [/= _|[hd1 hd2] tl IH /=].
- by rewrite M.elts_emp.
- case/ordset.OrderedSequence.ordered_inv => split_tl split_tl'.
  rewrite M.elts_union_sing; last by rewrite -M.elts_dom IH.
  by rewrite IH // Htl.
Qed.

Lemma size_dom_union h1 h2 : h1 # h2 ->
  size (dom (h1 \U h2)) = (size (dom h1) + size (dom h2))%nat.
Proof.
move/Permutation_dom_union/Permutation_size.
by rewrite size_cat.
Qed.

Lemma size_dom_difs k d : uniq d -> inc d (dom k) ->
  size (dom (k \D\ d)) = (size (dom k) - size d)%nat.
Proof.
move=> u_d d_k.
move: (proj_difs k d) => H.
rewrite {2}H size_dom_union; last exact/proj_difs_disj_spec.
by rewrite size_dom_proj_exact // addnC addnK.
Qed.

(* TODO: remove? *)
Lemma union_difs_L_old h1 h2 : h1 # h2 -> (h1 \U h2) \D\ dom h1 = h2.
Proof.
move=> h1_d_h2.
rewrite difs_union_L.
- by rewrite difs_self unioneh.
- by rewrite dis_sym -disjE.
Qed.

Lemma incl_dom_union h1 h2 : inc (dom h1) (dom (h1 \U h2)).
Proof. by apply/incP' => x xH; rewrite in_dom_union_L. Qed.

Lemma inclu_disj h1 h2 k : h1 # h2 -> k \I h1 -> k # h2.
Proof.
move=> h1_d_h2 k_h1; rewrite disjE; apply/(@dis_inc_L _ (dom h1));
  [by rewrite -disjE | exact/inclu_inc_dom].
Qed.

Lemma inclu_union h h1 h2 : h1 \I h -> h2 \I h -> (h1 \U h2) \I h.
Proof.
move=> h1_h h2_h; apply get_inclu => n w H.
case/get_union_Some_inv : H; by apply inclu_get.
Qed.

Lemma get_proj_Some_inv d (k : t) (n : l) y : get n (proj k d) = Some y -> n \in d.
Proof.
move=> H.
apply/negP => abs.
rewrite get_proj_None // in H.
by apply/negP.
Qed.

Lemma cdom_proj_LR h l1 l2 l3 : dom h = l1 ++ l2 ++ l3 ->
  cdom (h |P| l2) = drop (size l1) (take (size (l1 ++ l2)) (cdom h)).
Proof.
move=> hl123.
rewrite -(cdom_proj_L h (l1 ++ l2) l3); last by rewrite -catA.
rewrite (_ : proj h l2 = proj (proj h (l1 ++ l2)) l2); last first.
  rewrite proj_proj //; by apply inc_app_R.
apply cdom_proj_R.
rewrite dom_proj_exact //.
- move: (dom_ord h).
  move/OrderedSequence.orderedP.
  rewrite hl123 catA.
  by case/OrderedSequence.ordered_app_inv.
- rewrite hl123 catA; by apply inc_app_L.
Qed.

Lemma size0_emp : forall k, size (dom k) = O -> k = emp.
Proof.
move=> k Hsz.
apply dom_cdom_heap.
- destruct (dom k) => //; by rewrite dom_emp.
- rewrite -size_cdom_dom in Hsz.
  destruct (cdom k) => //; by rewrite cdom_emp.
Qed.

End Map_Prop.

(** Tactics for finite maps *)

Module Map_Tac (M : MAP).

Import M.
Notation "k '#' m" := (disj k m).
Notation "k '\U' m" := (union k m).

Lemma disj_up : forall x x1 x2 x3, x = x1 \U x3 -> x1 # x3 -> x # x2 -> x1 # x2.
Proof.
move=> h0 h1 h2 h3 H H'.
move/disj_sym => H''.
rewrite H in H''.
case: (disj_union_inv _ _ _ H'') => H3 _.
by apply disj_sym.
Qed.

Lemma disj_up' : forall x x1 x2 x3, x = x1 \U x3 -> x1 # x3 -> x # x2 -> x3 # x2.
Proof.
move=> h0 h1 h2 h3 H H'.
move/disj_sym => H''.
rewrite H in H''.
case: (disj_union_inv _ _ _ H'') => _ H3.
by apply disj_sym.
Qed.

Ltac Disj :=
  match goal with
    | H: (union ?x1 ?x2) # ?x |- _ =>
      let H1 := fresh in
      generalize (disj_union_inv x1 x2 x (disj_sym (union x1 x2) x H));
        intro H1; inversion_clear H1; clear H; Disj
    | H: ?x # (union ?x1 ?x2) |- _ =>
      let H1 := fresh in
      generalize (disj_union_inv x1 x2 x H); intro H1; inversion_clear H1; clear H; Disj
    | |- (union ?x1 ?x2) # ?x3 =>
      eapply disj_sym; apply disjhU; [ (Disj_simpl || Disj) | (Disj_simpl || Disj) ]
    | |- ?x3 # (union ?x1 ?x2) =>
      apply disjhU; [ (Disj_simpl || Disj) | (Disj_simpl || Disj) ]
    | |- ?x1 # ?x2 => Disj_up
  end
with
  Disj_up := Disj_simpl || Disj_up_left || Disj_up_right
with
  Disj_up_left :=
  match goal with
    | H1: ?X1 = (union ?x1 ?x1')  |- ?x1 # ?x2 =>
      apply (disj_up X1 x1 x2 x1' H1); [(Disj_simpl || Disj) | (Disj_simpl || Disj)]
    | H1: ?X1 = (union ?x1 ?x1')  |- ?x1' # ?x2 =>
      apply (disj_up' X1 x1 x2 x1' H1) ; [(Disj_simpl || Disj) | (Disj_simpl || Disj)]
    | |- ?x1 # ?x2 => Disj_simpl
  end
with
  Disj_up_right :=
  match goal with
    | H1: ?X1 = (union ?x2 ?x2')  |- ?x1 # ?x2 =>
      apply disj_sym; apply (disj_up X1 x2 x1 x2' H1); [(Disj_simpl || Disj) | (Disj_simpl || Disj)]
    | H1: ?X1 = (union ?x2 ?x2')  |- ?x1 # ?x2' =>
      apply disj_sym; apply (disj_up' X1 x2 x1 x2' H1) ; [(Disj_simpl || Disj) | (Disj_simpl || Disj)]
    | |- ?x1 # ?x2 => Disj_simpl
  end
with
  Disj_simpl :=
  match goal with
    | H : ?x1 # ?x2 |- ?x1 # ?x2 => auto
    | H : ?x2 # ?x1 |- ?x1 # ?x2 => apply disj_sym; auto
    | |- ?x1 # emp => apply (disjhe x1)
    | |- emp # ?x1 => apply disj_sym; apply (disjhe x1)
    | |- sing ?l1 ?v1 # sing ?l2 ?v2 => eapply disj_sing; lia
  end.

Lemma Disj_test1 : forall h h1 h2, h # (h1 \U h2) -> h # h2.
Proof. intros. by Disj. Qed.

Lemma Disj_test2 : forall h h1 h2 h11 h12 h21 h22 h111 h112 h121 h122 h211 h212 h221 h222,
  h1 # h2 ->
  h11 # h12 ->
  h21 # h22 ->
  h111 # h112 ->
  h121 # h122 ->
  h211 # h212 ->
  h221 # h222 ->
  h = h1 \U h2 ->
  h1 = h11 \U h12 ->
  h2 = h21 \U h22 ->
  h11 = h111 \U h112 ->
  h12 = h121 \U h122 ->
  h21 = h211 \U h212 ->
  h22 = h221 \U h222 ->
  (h112 \U h221) # h222.
Proof. intros. by Disj. Qed.

Lemma Equal_union_com h1 h2 h3 h4 : h1 # h2 ->
  h2 \U h1 = h3 \U h4 -> h1 \U h2 = h3 \U h4.
Proof. move=> H H0; by rewrite unionC. Qed.

Lemma Equal_subst: forall X h1 h2, h1 = h2 -> X \U h1 = X \U h2.
Proof. by move=> ? ? ? ->. Qed.

Ltac Equal :=
  match goal with
    | |-  (?h1 \U ?h2) = (?h1 \U ?h3) => apply (Equal_subst h1 h2 h3); Equal
    | |- ?h1 = ?h1 => auto
    | |- (emp \U ?h1) = ?h2 => rewrite (unioneh h1); Equal
    | |- (?h1 \U emp) = ?h2 => rewrite (unionhe h1); Equal
    | |- ?h2 = (emp \U ?h1)  => rewrite (unioneh h1); Equal
    | |- ?h2 = (?h1 \U emp) => rewrite (unionhe h1); Equal
    | H: ?X = (?x1 \U ?x2) |- (?X \U ?x1') = (?Y \U ?x2') => rewrite H ; Equal
    | H: ?Y = (?y1 \U ?y2) |- (?X \U ?x1') = (?Y \U ?x2') => rewrite H ; Equal
    | H: ?X = (?x1 \U ?x2) |- ?X = (?Y \U ?x2') => rewrite H ; Equal
    | H: ?Y = (?y1 \U ?y2) |- (?X \U ?x1') = ?Y => rewrite H ; Equal
    | |- ((?h1 \U ?h2) \U ?h3) = ?X => rewrite -(unionA h1 h2 h3); [Equal]
    | |- ?X = ((?h1 \U ?h2) \U ?h3)  => rewrite -(unionA h1 h2 h3); [Equal]
    | |- (?h1 \U ?h2) = (?h3 \U ?h4) => apply (Equal_union_com h1 h2 h3 h4); [Disj | Equal]
    | H1: ?h1 = ?h2 |- ?h1 = ?h3 => rewrite H1; Equal
    | H1: ?h1 = ?h2 |- ?h3 = ?h1 => rewrite H1; Equal
  end.

Ltac collect_until' x m seed :=
  match m with
    | union (sing x ?vx) ?m' =>
      seed
    | union (sing ?y ?vy) ?m' =>
      let seed' := constr: (union seed (sing y vy)) in
      collect_until' x m' seed'
    | sing x ?vx =>
      seed
    | sing ?y ?vy =>
      constr : (union seed (sing y vy))
  end.

Ltac collect_until x m :=
  match m with
    | union (sing x ?vx) ?m' =>
      constr: (emp)
    | union (sing ?y ?vy) ?m' =>
      let seed := constr: (sing y vy) in
      collect_until' x m' seed
    | sing x ?vx =>
      constr : (emp)
    | sing ?y ?vy =>
      constr : (sing y vy)
  end.

Ltac collect_after x m :=
  match m with
    | union (sing x ?vx) ?m' =>
      m'
    | union (sing ?y ?vy) ?m' =>
      collect_after x m'
    | union x ?vx =>
      constr: (emp)
    | sing ?y ?vy =>
      constr : (emp)
  end.

Ltac find_image x m :=
  match m with
    | union (sing x ?vx) ?m' => constr : ( Some vx )
    | union (sing ?y ?vy) ?m' => find_image x m'
    | sing x ?vx => constr : ( Some vx )
    | sing ?y ?vy => None
  end.

Ltac put_in_front x :=
  match goal with
    | |- context [union ?K ?L] =>
      let m := constr : (union K L) in
      let pre := collect_until x m in
      let pos := collect_after x m in
      let new_m := constr: (union pre pos) in
      let img := find_image x m in
      match img with
        | Some ?vx =>
          let ret := constr : (union (sing x vx) new_m) in
            rewrite (_ : union K L = ret);
              [ (repeat rewrite <- unionA ;
                 repeat rewrite unionhe ;
                 repeat rewrite unioneh) | (repeat rewrite <- unionA ;
                                            repeat rewrite unionhe ;
                                            repeat rewrite unioneh ;
                        Equal_union) ]
        | None => fail
      end
  end.

End Map_Tac.

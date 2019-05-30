(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import prime.
Require Import Max.
Require Import ssrZ ZArith_ext String_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import multi_int.

Local Open Scope machine_int_scope.
Local Open Scope zarith_ext_scope.

(** preamble *)

Definition Zmax_seq_opt (l : seq Z) (n : option Z) :=
  match n with
    | Some m => Z.max m (Zmax_seq l)
    | None => Z.max (Zmax_seq l) 1
  end.
Notation "Zmax( l , n )" := (Zmax_seq_opt l n) : rfc5246_scope.

Local Open Scope rfc5246_scope.

Module MachineIntByte_m.

Definition bytes2Z l : Z := bSum_c 8 l.
Definition bytes2nat l : nat := '| bSum_c 8 l |.
Definition nibble := int 4.

Definition hex2ot (l : string) : option (int 8) :=
  match l with
    | String h (String h' EmptyString) =>
      match oZ_of_hex h, oZ_of_hex h' with
        | Some a, Some b => Some (`( a )c_ 4 `|| `( b )c_ 4)
        | _, _ => None
      end
    | String h EmptyString => match oZ_of_hex h with Some a => Some (zext 4 (`( a )c_ 4)) | _ => None end
    | EmptyString => Some (`( 0 )c_ 8)
    | _ => None
  end.

Lemma hex2ot_all : forall l, hex2ot l == None ->
  (~~ all (fun x : Ascii.ascii => oZ_of_hex x != None) (string2asciis l))
  || (String.length l > 2)%nat.
Proof.
elim=> // h [] //.
  move=> _ /=.
  by destruct (oZ_of_hex h).
move=> h' [] //; last first.
  move=> *; apply/orP; by right.
rewrite /=.
destruct (oZ_of_hex h) => //.
by destruct (oZ_of_hex h').
Qed.

Program Definition hex2t (l : string) 
  (H : (all (fun x => oZ_of_hex x != None) (string2asciis l)) && (String.length l <= 2)%nat) : int 8 :=
  match hex2ot l with 
      | Some z => z
      | None => False_rect _ _
  end.
Next Obligation.
move: H.
apply/negP.
rewrite negb_and leqNgt negbK.
apply hex2ot_all.
by apply/eqP.
Defined.

End MachineIntByte_m.

Notation "'\0x' l" := (MachineIntByte_m.hex2t l Logic.eq_refl) (at level 9) : rfc5246_scope.

Module RFC5246.

(** * 4. Presentation Language *)

Definition byte : Type := int 8.

(** ** 4.1 Basic Block Size *)

Module S41.
Definition bytes2Z (l : seq byte) := MachineIntByte_m.bytes2Z l.
Definition bytes2nat (l : seq byte) := MachineIntByte_m.bytes2nat l.
End S41.

Notation "'nat<=i8'" := (S41.bytes2nat) (at level 9).

(** A type for vectors, enumerateds, and constructed types
   (variants will be represented by Coq records).
   - The type carries the min/max number of bytes required for
   encoding as list of bytes.
   - Divisibility is type-checked for fixed-size vectors.
   - Bounds inclusion is type-checked for variable-size vectors.
   NB: According to the RFC (p.9), "the length of an encoded vector
   must be an even multiple of the length of a single element".
   But we do not add this divisibility check because "extensions"
   allow for nested variable-size vectors.
   - Enumerated and variable-size vectors carry the number
   of bytes necessary to encode their size.
   *)

Inductive tls_typ : Z -> Z -> Type :=
| opaque : tls_typ 1 1
| arr : forall n, tls_typ n n -> forall m, 0 <=? m -> 
  m mod n == 0 -> 
  tls_typ m m
| varr : forall n m (t : tls_typ n m) (k : nat) a b, a <=? b -> 
  k != O -> b <? 2^^(k * 8) -> 2^^((k - 1) * 8) <=? b -> m <=? Z<=nat k + b ->
  tls_typ (Z<=nat k + a) (Z<=nat k + b)
| enum : forall k l n, uniq l ->
  Zmax(l, n) <? 2^^(k * 8) -> 2^^((k - 1) * 8) <=? Zmax(l, n) ->
  tls_typ (Z<=nat k) (Z<=nat k)
| pair : forall {n1 m1 n2 m2},
  string * tls_typ n1 m1 -> tls_typ n2 m2 -> 
  tls_typ (n1 + n2) (m1 + m2)
| typ_nil : tls_typ 0 0.

Section tls_typ_ind_nested.

Variables (P : forall a b, tls_typ a b -> Prop) .
Hypotheses (H0 : P 0 0 typ_nil) (H1 : P 1 1 opaque)
(H2 : forall n (t : tls_typ n n), P n n t ->
      forall m (i : 0 <=? m) (i0 : m mod n == 0), P m m (arr n t m i i0))
(H3 : forall n m (t : tls_typ n m), P n m t -> forall (k : nat) a b 
      (ab : a <=? b) (i : k != O) (i0 : b <? 2 ^^ (k * 8)) 
      (i1 : 2 ^^ ((k - 1) * 8) <=? b) (i3 : m <=? Z_of_nat k + b),
      P (Z_of_nat k + a) (Z_of_nat k + b) (varr n m t k _ _ ab i i0 i1 i3))
(H4 : forall (k : nat) (l : seq Z) n  (i : uniq l) 
      (i0 : Zmax(l, n) <? 2 ^^ (k * 8))
      (i1 : 2 ^^ ((k - 1) * 8) <=? Zmax(l, n)),
      P (Z_of_nat k) (Z_of_nat k) (enum k l n i i0 i1)).

Section gen.

Variable (Q : forall a b, string * tls_typ a b -> Prop).
Hypotheses 
(PQ : forall a b t, P a b t -> forall s, Q a b (s, t))
(H : forall n1 m1 n2 m2 (p : string * tls_typ n1 m1) (t : tls_typ n2 m2), 
     Q n1 m1 p -> P n2 m2 t -> P (n1 + n2) (m1 + m2) (pair p t)).

Fixpoint tls_typ_nested_ind' a b t : P a b t :=
  match t as x return P _ _ x with
    | opaque => H1 
    | arr n t' m i i0 => H2 n t' (tls_typ_nested_ind' _ _ t') m i i0
    | varr n m t' k _ _ ab Hk i1 i2 i3 => H3 n m t' (tls_typ_nested_ind' _ _ t') k _ _ ab Hk i1 i2 i3
    | enum k l n i i0 i1 => H4 k l n i i0 i1 
    | pair n1 m1 n2 m2 p t' => H n1 m1 n2 m2 p t' 
      match p as x return Q n1 m1 x with
         | (p1, p2) => PQ _ _ _ (tls_typ_nested_ind' _ _ p2) p1
      end
      (tls_typ_nested_ind' _ _ t')
    | typ_nil => H0
  end.

End gen.

Section spe.

Hypothesis H : 
  (forall a b c d s t1 t2, P a b t1 -> P c d t2 -> P _ _ (pair (s, t1) t2)).

Lemma tls_typ_nested_ind : forall a b (t : tls_typ a b) , P _ _ t.
Proof.
apply tls_typ_nested_ind' with (fun a b p => forall x, x = snd p -> P _ _ x) => //.
- move=> a b t HP s x Hx; by subst x.
- move=> n1 m1 n2 m2 [p1 p2] t Hp2 Ht.
  apply H => //.
  by apply Hp2.
Qed.

End spe.

End tls_typ_ind_nested.

Notation "'struct{' a ; .. ; b '}'" := (pair a .. (pair b typ_nil) ..) (at level 10, no associativity,
  format "'[v' 'struct{' a ; .. ; b '}' ']'").
Notation "'struct{}'" := typ_nil.

Fixpoint tls_typ_find_struct_tag {n m} (t : tls_typ n m) (tag : string) : bool :=
match t with
  | pair _ _ _ _ tag' t' => if tag == fst tag' then false else tls_typ_find_struct_tag t' tag
  | _ => true
end.

Fixpoint tls_typ_well_formed {n m} (t : tls_typ n m) : bool :=
match t with
  | opaque => true
  | arr _ t _ _ _ => tls_typ_well_formed t
  | varr _ _ t _ _ _ _ _ _ _ _ => tls_typ_well_formed t
  | enum _ _ _ _ _ _ => true
  | pair _ _ _ _ (tg, rem) tr => tls_typ_well_formed rem && negb (tls_typ_find_struct_tag tr tg) &&
    match tr with
      | pair _ _ _ _ _ _ => tls_typ_well_formed tr
      | typ_nil => true
      | _ => false
    end
  | typ_nil => true
end.

Definition lst_enum {n m} (t : tls_typ n m) : seq Z :=
  if t is enum _ l _ _ _ _ then l else nil.

Fixpoint tls_max {n m} (t : tls_typ n m) : Z :=
  match t with
    | opaque => m
    | arr _ _ _ _ _ => m
    | varr _ _ _ k _ _ H1 H2 H3 H4 H5 => m - Z_of_nat k
    | enum _ _ _ _ _ _ => m
    | pair _ _ _ _ (_, t1) t2 => tls_max t1 + tls_max t2
    | typ_nil => m
  end.

Fixpoint tls_min {n m} (t : tls_typ n m) : Z :=
  match t with
    | opaque => n
    | arr _ _ _ _ _ => n
    | varr _ _ _ k _ _ H1 H2 H3 H4 H5 => n - Z_of_nat k
    | enum _ _ _ _ _ _ => n
    | pair _ _ _ _ (_, t1) t2 => tls_min t1 + tls_min t2
    | typ_nil => n
  end.

Fixpoint depth {n m} (t : tls_typ n m) :=
  match t with
    | opaque => O
    | arr _ t _ _ _ => S (depth t)
    | varr _ _ t' _ _ _ _ _ _ _ _ => S (depth t')
    | enum m _ _ _ _ _ => O
    | pair _ _ _ _ (_, t1) t2 => S (max (depth t1) (depth t2))
    | typ_nil => O
  end.

Section tls_typ_decoding.

(** A function to decide whether (the beginning of) a list of bytes is the implementation of a tls_typ. *)
Fixpoint decode' k {n m} (t : tls_typ n m) (l : seq byte)
  : bool * seq byte :=
  match k with
    | O =>
      match t with
        | opaque => if (1 <= size l)%nat then
                      (true, behead l)
                    else
                      (false, l)
        | arr n _ m _ _ => if m <=? Z_of_nat (size l) then
                             (true, drop '|m| l)
                           else
                             (false, l)
        | varr n m t' x k a b _ _ _ _ => (false, l) (* NB: cannot happen at this depth *)
        | enum m l' _ _ _ _ => if (m <= size l)%nat && ((S41.bytes2Z (take m l)) \in l') then
                                (true, drop m l)
                              else
                                (false, l)
        | pair n1 m1 n2 m2 (tg, t1) t2 => (false, l) (* NB: cannot happen at this depth *)
        | typ_nil => (true, l)
      end
    | S k' =>
      match t with
        | opaque => if (1 <= size l)%nat then
                      (true, behead l)
                    else
                      (false, l)
        | arr n _ m _ _ => if m <=? Z<=nat (size l) then
                             (true, drop '|m| l) (* TODO: no enum in arr thus ok but may need a recursive call *)
                           else
                             (false, l)
        | varr n m t' k a b _ _ _ _ _ =>
          if (k <= size l)%nat then
            let len := S41.bytes2nat (take k l) in
            if (len <= size (drop k l))%nat then
              let (ret, l') := foldl
                (fun a _ =>  match a with | (acc, buf) =>
                      match buf with
                        | nil => a
                        | _ => if acc then
                                 let (acc', buf') := decode' k' t' buf in (acc' && acc, buf')
                               else
                                 (acc, buf)
                      end
                  end)
                (true, take len (drop k l)) 
                (nseq len tt) (* NB: upper bound on the number of recursive calls to be done *)
                in
              if ret then
                (true, l' ++ drop len (drop k l))
              else
                (false, l)
            else
              (false, l)
          else
            (false, l)
        | enum m l' _ _ _ _ => if (m <= size l)%nat && ((S41.bytes2Z (take m l)) \in l') then
                                (true, drop m l)
                              else
                                (false, l)
        | pair n1 m1 n2 m2 (tg, t1) t2 =>
          let: (a, l') := decode' k' t1 l in
          let: (a', l'') := decode' k' t2 l' in
          (a && a', l'')
        | typ_nil => (true, l)
      end
  end.

End tls_typ_decoding.

Lemma decode'_upper : forall a b (t : tls_typ a b) n l, (depth t <= n)%nat ->
  decode' (depth t) t l = decode' n t l.
Proof.
move=> a b; elim/tls_typ_nested_ind => // {a b}.
- by case.
- by case.
- by move=> n t IH a H1 _ [] //.
- move=> n m t IH l' a b H1 H2 H3 H4 H5 n0 l /= Hn0.
  destruct n0 as [|n0]; [done | move=> /=].
  move Hfold1 : (foldl _ _ _) => fold1.
  move Hfold2 : (foldl _ _ _) => fold2.
  suff : fold1 = fold2 by move=> ->.
  rewrite -{}Hfold1 -{}Hfold2.
  apply foldl_ext => x [a0 a1] Hx.
  move Hdec1 : (decode' _ _ _) => dec1.
  move Hdec2 : (decode' _ _ _) => dec2.
  suff : dec1 = dec2 by move=> ->.
  rewrite -{}Hdec1 -{}Hdec2.
  by apply IH.
- by move=> m l n Hnodup H1 H2 [].
- move=> n1 m1 n2 m2 tag t1 t2 IH1 IH2 n l /= Hmax.
  destruct n as [|n]; first by done.
  rewrite -IH1 /=; last by apply/leP; apply le_max_l.
  symmetry.
  rewrite -IH1 /=; last first.
    move: Hmax. rewrite ltnS. move/leP. move/max_lub_l. by move/leP.
  move Hdec1 : (decode' _ _ _) => [dec11 dec12].
  rewrite -IH2 //; last first.
    move: Hmax. rewrite ltnS. move/leP. move/max_lub_r. by move/leP.
  symmetry.
  rewrite -IH2 //.
  by apply/leP; apply le_max_r.
Qed.

Lemma fold_decode'_false : forall a b (t : tls_typ a b) lst l,
  foldl
  (fun (a : bool * seq byte) (_ : unit) =>
    let (acc, buf) := a in
      if acc then
        let (acc', buf') := decode' (depth t) t buf in
          (acc' && acc, buf')
      else
        (acc, buf))
  (false, l) 
  lst = (false, l).
Proof. move=> a b t; by elim. Qed.

Definition decode {n m} (t : tls_typ n m) := decode' (depth t) t.

(** A predicate to decide whether a list of bytes is the implementation of a tls_typ. *)
Definition decodep {n m} (t : tls_typ n m) (l : seq byte) :=
  let (a, l'):= decode t l in a && (size l' == O).

Lemma decode_app : forall n m (t : tls_typ n m) a a' b,
  decode t a = (true, a') -> decode t (a ++ b) = (true, a' ++ b).
Proof.
move=> n m; elim/tls_typ_nested_ind => {n m}.
- (* str_nil *) move => a a' b H.
  rewrite /decode /= in H *.
  by inversion H.
- (* opaque *) move=> a a' b.
  rewrite /decode /=.
  case: ifP.
  + move=> Ha [] ?; subst a'.
    rewrite size_cat addn_gt0 Ha /=.
    by destruct a.
  + by destruct a.
- (* arr *) move=> n t IH m m0 m_n a a' b.
  rewrite /decode /=.
  case: ifP => // m_a [] ?; subst a'.
  rewrite size_cat inj_plus.
  have -> : m <=? Z_of_nat (size a) + Z_of_nat (size b).
    move/leZP in  m_a.
    apply/leZP.
    rewrite addZC.
    apply leZ_addl; [exact: Zle_0_nat | by []].
    rewrite drop_cat.
    case: ifP => // H.
    have : '|m| = size a.
      move/leZP in m_a.
      move/negbT in H.
      rewrite -leqNgt in H.
      have {m_a}m_a : ('|m| <= '|Z_of_nat (size a)|)%nat.
        apply/leP.
        apply Zabs_nat_le.
        split => //.
        by move/leZP in m0.
      rewrite Zabs2Nat.id // in m_a.
      by apply/eqP; rewrite eqn_leq H m_a.
    move=> ->; by rewrite subnn drop0 drop_size.
- (* varr *) move=> n m t IH l' n' m' H1 H2 H3 H4 H5 a a' b.
  rewrite /decode /=.
  case: ifP => // l'_a.
  case: ifP => // Hheader.
  move Hfold1 : (foldl _ _ _) => [ret1 buf1].
  move Hfold2 : (foldl _ _ _) => [ret2 buf2].
  case: ifP => // Hret1 [] ?; subst a'.
  have Z : (l' <= size (a ++ b))%nat.
    rewrite size_cat -(addn0 l'); by apply leq_add.
  rewrite Z.
  have X : take l' a = take l' (a ++ b).
    by rewrite takel_cat.
  rewrite -X in Hfold2.
  have Y : (drop l' a) ++ b = drop l' (a ++ b).
    rewrite drop_cat.
    case: ifP => //.
    move/negbT.
    rewrite -leqNgt => H.
    have {H}H : size a = l' by apply/eqP; rewrite eqn_leq H l'_a.
    by rewrite -H drop_size subnn drop0.
  rewrite -X -Y size_cat -(addn0 (S41.bytes2nat (take l' a))) leq_add //.
  rewrite Hret1 in Hfold1.
  rewrite -Y takel_cat // in Hfold2.
  case: ifP => Hret2.
  + rewrite Hret2 Hfold1 in Hfold2.
    case: Hfold2 => ?; subst buf2.
    congr (_, _).
    rewrite drop_cat.
    case: ifP => // H.
    by rewrite catA.
    move/negbT in H.
    rewrite -leqNgt addn0 in H.
    have {H}H : size (drop l' a) = nat<=i8 (take l' a) by apply/eqP; rewrite eqn_leq Hheader H.
    by rewrite -H addn0 subnn drop0 drop_size cats0.
  + subst ret2.
    by rewrite Hfold1 in Hfold2.
- (* enum *) move=> m l n Hnodup H1 H2 a a' b.
  rewrite /decode /=.
  case: ifP => //.
  case/andP => m_a Hinb [] ?; subst a'.
  rewrite size_cat -{1}(addn0 m) leq_add //= takel_cat //.
  rewrite Hinb.
  rewrite drop_cat.
  case: ifP => //.
  move/negbT.
  rewrite -leqNgt => H.
  have {H}H : m = size a by apply/eqP; rewrite eqn_leq m_a H.
  by rewrite -H subnn drop0 H drop_size.
- (* pair *) move=> n1 m1 n2 m2 tag t1 t2 IH1 IH2 a a' b.
  rewrite /decode /= -decode'_upper; last by apply/leP; apply le_max_l.
  move Hdec1 : (decode' _ _ _) => [dec11 dec12].
  rewrite -decode'_upper; last by apply/leP; apply le_max_r.
  move Hdec2 : (decode' _ _ _) => [dec21 dec22].
  case=> decx1 Ha'.
  subst dec22.
  destruct dec11; last by done.
  destruct dec21; last by done.
  rewrite {decx1} -decode'_upper; last by apply/leP; apply le_max_l.
  move/(IH1 _ _ b) : Hdec1.
  rewrite /decode => ->.
  rewrite -decode'_upper; last by apply/leP; apply le_max_r.
  move/(IH2 _ _ b) : Hdec2.
  by rewrite /decode => ->.
Qed.

(** Extract the fixed-size part of a tls_type. *)
Fixpoint fixed_sz {n m} (t : tls_typ n m) : Z :=
  match t with
    | opaque => 1
    | arr _ _ m _ _ => m
    | varr _ _ _ x _ _ _  _ _ _ _ => Z_of_nat x
    | enum m _ _ _ _ _ => Z_of_nat m
    | pair _ _ _ _ t1 t2 => fixed_sz (snd t1) + fixed_sz t2
    | str_nil => 0
  end.

(** Notations for tls_type *)
Notation "T \[ n \]" := (arr _ T n Logic.eq_refl Logic.eq_refl) (at level 50) : rfc5246_scope.

Notation "T \[[ n \]]" := (arr _ T (Z.abs n) (Zle_imp_le_bool _ _ (normZ_ge0 _))
  (proj1 (Zeq_is_eq_bool _ _) (Zmod_1_r (Z.abs n)))) (at level 50) : rfc5246_scope.

Notation "T `< a \.. b `> n " :=
  (varr _ _ T n a b Logic.eq_refl Logic.eq_refl Logic.eq_refl Logic.eq_refl Logic.eq_refl) (at level 50) : rfc5246_scope.

Notation "\enum n \{ lst \}" :=
  (enum n (map (@u2Zc 8) lst) None Logic.eq_refl Logic.eq_refl Logic.eq_refl) (at level 50) : rfc5246_scope.
Notation "\enum n \{ lst \} m" :=
  (enum n (map (@u2Zc 8) lst) (Some m) Logic.eq_refl Logic.eq_refl Logic.eq_refl) (at level 50).

(** ** 4.4 Numbers *)

(* NB: we put Section 4.4 before 4.3 *)
Module S44.
(* NB: implicit in the RFC *)
Definition uint8 := opaque.
Definition uint16 := uint8 \[ 2 \].
Definition uint24 := uint8 \[ 3 \].
Definition uint32 := uint8 \[ 4 \].
Definition uint64 := uint8 \[ 8 \].
End S44.

(** ** 4.3 Vectors *)
Module S43.
Definition Datum := opaque \[ 3 \].
Definition Data := Datum \[ 9 \].
(* Datum \[ 8 \]. does not type because ~ (3 | 8) *)
Definition Data' := opaque \[ 8 \].
Definition Data'' n := opaque \[[ n \]].
(* Definition Data''' n := Datum \[[ n \]]. fails *)
Definition mandatory := opaque `< 300 \.. 400 `> 2.
Import S44.
Definition longer := uint16 `< 0 \.. 800 `> 2.
End S43.

(** ** 4.5 Enumerateds *)

Module S45.
Definition red := `( 3 )c_8. Definition blue := `( 5 )c_8. Definition white := `( 7 )c_8.
Definition Color := \enum 1 \{ red :: blue :: white :: nil \}.
Definition sweet := `( 1 )c_8 . Definition sour := `( 2 )c_8. Definition bitter := `( 4 )c_8.
Definition Taste := \enum 2 \{ sweet :: sour :: bitter ::nil \} 32000.
End S45.

(** *** 4.6.1 Variants

   Encoded with Coq records. *)

Notation "'\{' i ; .. ; j '\}'":= (cons i .. (cons j nil) ..) (at level 70,
  format "'[v' '\{'  '//' i ';' '//' .. ';' '//' j '//' '\}' ']'", i at level 71, j at level 71) : select_scope.

Definition pack {n m} (T : tls_typ n m) : {n : Z & { m : Z & tls_typ n m } } 
 := existT (fun x => {m : Z & tls_typ x m}) n (existT _ m T).

Definition unpack (H : {n : Z & { m : Z & tls_typ n m } } ) :
  tls_typ (projT1 H) (projT1 (projT2 H)) := projT2 (projT2 H).

Module select_m.
Fixpoint sel {A :eqType} (l : seq (A * {n : Z & { m : Z & tls_typ n m } })) (z : A) :=
  match l with
    | (hi, ho) :: tl => if hi == z then ho else sel tl z
    | _ => pack typ_nil
  end.

Definition sel_test {A : eqType} (lst : seq A) (l : seq (A * {n : Z & {m : Z & tls_typ n m} }))
  (_ : all (fun x => fst x == snd x) (zip lst (unzip1 l)))
  (z : A) :=
  match lst with
    | nil => pack typ_nil
    | h :: t => if all (fun x => fst x == snd x) (zip lst (unzip1 l)) then
                  sel l z
                else
                  pack typ_nil
  end.

Definition sel_enum (z : seq byte) {n m} (t : tls_typ n m) (Henum : decodep t z)
  (l : seq (Z * {n' : Z & {m' : Z & tls_typ n' m'} }))
  (H : all (fun x => fst x == snd x) (zip (lst_enum t) (unzip1 l)))
  (H' : size l == size (lst_enum t)) :=
  sel_test (lst_enum t) l H (S41.bytes2Z z).
End select_m.

(** Notations for "select" *)
(*
Notation "'\{' i ; .. ; j '\}'":= (cons i .. (cons j nil) ..) (at level 70,
  format "'[v' '\{'  '//' i ';' '//' .. ';' '//' j '//' '\}' ']'", i at level 71, j at level 71) : select_scope.
*)
Notation "'selectb(' b '\)' lst" := (select_m.sel_test (false :: true :: nil) lst (refl_equal _) b) (at level 70,
  format "'[' 'selectb('  b  '\)' lst  ']' '//'") : select_scope.
Notation "'select(' z '\:' t '\:' H '\)' lst" := (select_m.sel_enum z t H lst (refl_equal _) (refl_equal _)) (at level 70,
  format "'[' 'select(' z '\:' t '\:' H '\)'  lst  ']' '//'") : select_scope.

Record packet (p : seq byte -> bool) : Type := {
  body :> seq byte ;
  decodable : p body }.
Arguments body [p].

(* Extract the variable size of a packet *)
Definition var_sz {n m} {t : tls_typ n m} (p : packet (decodep t)) :=
  (size p - '|(fixed_sz t)|)%nat.

Module dselect_m.
Fixpoint sel {A :eqType} (l : seq (A * (seq byte -> bool))) (z : A) :=
  match l with
    | (hi, ho) :: tl => if hi == z then ho else sel tl z
    | _ => fun _ => false
  end.

Definition sel_test {A : eqType} (lst : seq A) (l : seq (A * (seq byte -> bool)))
  (_ : all (fun x => fst x == snd x) (zip lst (unzip1 l)))
  (z : A) :=
  match lst with
    | nil => fun _ => false
    | h :: t => if all (fun x => fst x == snd x) (zip lst (unzip1 l)) then
                  sel l z
                else
                  fun _ => false
  end.

Definition sel_enum (z : seq byte) {n m} (t : tls_typ n m) (Henum : decodep t z)
  (l : seq (Z * (seq byte -> bool)))
  (H : all (fun x => fst x == snd x) (zip (lst_enum t) (unzip1 l))) :=
  sel_test (lst_enum t) l H (S41.bytes2Z z).
End dselect_m.

(*Notation "'\{' i ; .. ; j '\}'":= (cons i .. (cons j nil) ..) (at level 70,
  format "'[v' '\{'  '//' i ';' '//' .. ';' '//' j '//' '\}' ']'", i at level 71, j at level 71) : select_decode_scope.*)
Notation "'dselectb(' b '\)' lst" := (dselect_m.sel_test (false :: true :: nil) lst (refl_equal _) b) (at level 70,
  format "'[' 'dselectb('  b  '\)' lst  ']' '//'") : select_scope.
Notation "'dselect(' z '\:' t '\:' H '\)' lst" := (dselect_m.sel_enum z t H lst (refl_equal _)) (at level 70,
  format "'[' 'dselect(' z '\:' t '\:' H '\)'  lst  ']' '//'") : select_scope.

Local Open Scope string_scope.

Module S461.
Definition apple : byte := `( 0 )c_8. Definition orange := `( 1 )c_8. Definition banana := `( 2 )c_8.
Definition VariantTag := \enum 1 \{ apple :: orange :: banana :: nil \}.
Definition variable_string_type := opaque `< 0 \.. 10 `> 1.
  Definition fixed_string_type := opaque \[ 10 \].
Import S44.

Definition V1 :=
   struct{ ("number", uint16) ;
           ("string", variable_string_type) }.
Definition V2 :=
   struct{ ("number", uint32) ;
           ("string", fixed_string_type) }.

(** We know that [n] is really an element of VariantTag because of [Hn].
    NB: This is the encoding of the typed data, not the type only.
    NB: the select is defined with enum types, but in S7412 it will be used w.r.t. to a boolean.
<<
struct {
  select (VariantTag) {
    case apple:
      V1;
    case orange:
    case bananana:
      V2;
  } variant_body;
} VariantRecord;
>>
*)

Local Open Scope select_scope.

Definition VariantStructure n (Hn : decodep VariantTag n) :=  struct{
  ("variant_body", unpack (select(_ \: _ \: Hn \) \{
    (u2Zc apple, pack V1) ;
    (u2Zc orange, pack V2) ;
    (u2Zc banana, pack V2) \})) }.

Local Close Scope select_scope.

End S461.

(** ** 4.8 Constants *)
Module S48.
Import S44.
Definition Example1 :=
  struct{ ("f1", uint8) ;
          ("f2", uint8) }.
End S48.

(** ** 7.1 Change Cipher Spec Protocol *)
Module S71.
Definition change_cipher_spec : byte := `( 1 )c_8.
Definition type_type := \enum 1 \{ change_cipher_spec :: nil \} 255.
Definition ChangeCipherSpec := struct{
  ("type", type_type)
}.
End S71.

(** ** 7.2 Alert Protocol *)
Module S72.
Definition warning := `( 1 )c_8. Definition fatal := `( 2 )c_8.
Definition AlertLevel := \enum 1 \{ warning :: fatal :: nil \} 255.
Definition close_notify := `( 0 )c_8.
Definition unexpected_message := `( 10 )c_8.
Definition bad_record_mac := `( 20 )c_8.
Definition decryption_failed_RESERVED := `( 21 )c_8.
Definition record_overflow := `( 22 )c_8.
Definition decompression_failure := `( 30 )c_8.
Definition handshake_failure := `( 40 )c_8.
Definition no_certificate_RESERVED := `( 41 )c_8.
Definition bad_certificate := `( 42 )c_8.
Definition unsupported_certificate := `( 43 )c_8.
Definition certificate_revoked := `( 44 )c_8.
Definition certificate_expired := `( 45 )c_8.
Definition certificate_unknown := `( 46 )c_8.
Definition illegal_parameter := `( 47 )c_8.
Definition unknown_ca := `( 48 )c_8.
Definition access_denied := `( 49 )c_8.
Definition decode_error := `( 50 )c_8.
Definition decrypt_error := `( 51 )c_8.
Definition export_restriction_RESERVED := `( 60 )c_8.
Definition protocol_version := `( 70 )c_8.
Definition insufficient_security := `( 71 )c_8.
Definition internal_error := `( 80 )c_8.
Definition user_canceled := `( 90 )c_8.
Definition no_renogociation := `( 100 )c_8.
Definition unsupported_extension := `( 110 )c_8.
Definition AlertDescription := \enum 1 \{
close_notify :: unexpected_message :: bad_record_mac :: decryption_failed_RESERVED ::
record_overflow :: decompression_failure :: handshake_failure :: no_certificate_RESERVED ::
bad_certificate :: unsupported_certificate :: certificate_revoked :: certificate_expired ::
certificate_unknown :: illegal_parameter :: unknown_ca :: access_denied :: decode_error ::
decrypt_error :: export_restriction_RESERVED :: protocol_version :: insufficient_security ::
internal_error :: user_canceled :: no_renogociation :: unsupported_extension :: nil\} 255.
Definition Alert :=
   struct{ ("level",       AlertLevel) ;
           ("description", AlertDescription) }.
End S72.

(** **** Hello Extensions *)
(* NB: we put Section 7.4.1.4.1 before Section 4.7 *)
Module S74141.
Definition none := `( 0 )c_8. Definition md5 := `( 1 )c_8. Definition sha1 := `( 2 )c_8.
Definition sha224 := `( 3 )c_8. Definition sha256 := `( 4 )c_8. Definition sha384 := `( 5 )c_8.
Definition sha512 := `( 6 )c_8.
Definition HashAlgorithm := \enum 1
  \{ none :: md5 :: sha1 :: sha224 :: sha256 :: sha384 :: sha512 :: nil \} 255.
Definition anonymous := `( 0 )c_8. Definition rsa := `( 1 )c_8.
Definition dsa := `( 2 )c_8. Definition ecdsa := `( 3 )c_8.
Definition SignatureAlgorithm := \enum 1
  \{ [:: anonymous ; rsa ; dsa ; ecdsa] \} 255.
Definition SignatureAndHashAlgorithm :=
   struct{ ("hash",      HashAlgorithm) ;
           ("signature", SignatureAlgorithm) }.
Definition supported_signature_algorithms :=
  SignatureAndHashAlgorithm `< 2 \.. (2 ^ 16 - 2) `> 2.
End S74141.

(** ** Cryptographic Attributes *)
Module S47.
(*Definition signature_type := opaque \< 2 \.. (2 ^ 16 - 1) \> 2.*)
Import S74141.
Definition DigitallySigned :=
   struct{ ("algorithm", SignatureAndHashAlgorithm) ;
           ("signature", opaque `< 2 \.. (2 ^ 16 - 1) `> 2) }.
End S47.

(** * 6. The TLS Record Protocol *)

(** ** 6.1 Connection States *)
Module S61.
Definition server := `( 0 )c_8. Definition client := `( 1 )c_8.
Definition ConnectionEnd := \enum 1 \{  server :: client :: nil \}.
Definition tls_prf_sha256 := `( 0 )c_8.
Definition PRFAlgorithm := \enum 1 \{ tls_prf_sha256 :: nil \}.
Definition null_bca := `( 0 )c_8.
(* NB : _bca to distinguish from null of CompressionMethod *)
Definition rc4 := `( 1 )c_8. Definition threedes := `( 2 )c_8. Definition aes := `( 3 )c_8.
Definition BulkCipherAlgorithm := \enum 1 \{ null_bca :: rc4 :: threedes :: aes :: nil \}.
Definition stream := `( 0 )c_8. Definition block := `( 1 )c_8. Definition aead := `( 2 )c_8.
Definition CipherType := \enum 1 \{ stream :: block :: aead :: nil \}.
Definition null_ma := `( 0 )c_8.
(* NB : _ma to distinguish from null of CompressionMethod *)
Definition hmac_md5 := `( 1 )c_8. Definition hmac_sha1 := `( 2 )c_8. Definition hmac_sha256 := `( 3 )c_8.
Definition hmac_sha384 := `( 4 )c_8. Definition hmac_sha512 := `( 5 )c_8.
Definition MACAlgorithm := \enum 1 \{ null_ma :: hmac_md5 :: hmac_sha1 :: hmac_sha256 ::
  hmac_sha384 :: hmac_sha512 :: nil \}.
Definition null := `( 0 )c_8.
Definition CompressionMethod := \enum 1 \{ [:: null] \} 255.
Import S44.
Definition SecurityParameters :=
  struct{ ("entity",                ConnectionEnd) ;
          ("prf_algorithm",         PRFAlgorithm) ;
          ("bulk_cipher_algorithm", BulkCipherAlgorithm) ;
          ("cipher_type",           CipherType) ;
          ("enc_key_length",        uint8) ;
          ("block_length",          uint8) ;
          ("fixed_iv_length",       uint8) ;
          ("record_iv_length",      uint8) ;
          ("mac_algorithm",         MACAlgorithm) ;
          ("mac_length",            uint8) ;
          ("mak_key_length",        uint8) ;
          ("compression_algorithm", CompressionMethod) ;
          ("master_secret",         opaque \[ 48 \]) ;
          ("client_random",         opaque \[ 32 \]) ;
          ("server_random",         opaque \[ 32 \]) }.
End S61.

(** *** 6.2.1 Fragmentation *)
Module S621.
Import S44.
Definition ProtocolVersion :=
  struct{ ("major", uint8) ; ("minor", uint8) }.
Definition change_cipher_spec := `( 20 )c_8.
Definition alert := `( 21 )c_8.
Definition handshake := `( 22 )c_8.
Definition application_data := `( 23 )c_8.
Definition ContentType := \enum 1 \{ change_cipher_spec :: alert :: handshake :: application_data :: nil \} 255.
(** remark p.20: *)
Definition length_maxp (x : seq byte) := (S41.bytes2nat x <= 2 ^ 14)%nat.

Definition SSLv30_maj := `( 3 )_ 8.
Definition SSLv30_min := `( 0 )_ 8.
Definition TLSv10_maj := SSLv30_maj.
Definition TLSv10_min := `( 1 )_8.
Definition TLSv11_maj := SSLv30_maj.
Definition TLSv11_min := `( 2 )_8.
Definition TLSv12_maj := SSLv30_maj.
Definition TLSv12_min := `( 3 )_8.

Definition is_maj x := x \in [:: SSLv30_maj; TLSv10_maj; TLSv11_maj; TLSv12_maj].
Definition is_min x := x \in [:: SSLv30_min; TLSv10_min; TLSv11_min; TLSv12_min].
Definition proverp s := is_maj s `_ O && is_min s `_ 1.

Structure TLSPlainText := {
  type : packet (decodep ContentType) ;
  version : packet (fun x => decodep ProtocolVersion x && proverp x) ;
  length : packet (fun x => decodep uint16 x && length_maxp x) ;
  fragment : packet (decodep (opaque \[[ S41.bytes2Z length \]]))
}.

Definition TLSPlainText_header_decode l : bool * seq byte :=
  let (a1, l1) := decode ContentType l in
  let (a2, l2) := let (a2', l2) := decode ProtocolVersion l1 in
                  (a2' && proverp (take '|(fixed_sz ProtocolVersion)| l1), l2) in
  let (a3, l3) := let (a3', l3) := decode uint16 l2 in
                  (a3' && length_maxp (take '|(fixed_sz uint16)| l2), l3) in
  ([&& a1, a2 & a3], l3).

Definition TLSPlainText_hd :=
  fixed_sz ProtocolVersion + fixed_sz ContentType + fixed_sz uint16.

End S621.

(** *** 6.2.2 Record Compression and Decompression *)
Module S622.
Import S621 S44.
(** remark p. 21: *)
Definition length_max := (2 ^ 14 + 1024)%nat.
Structure TLSCompressed_packet := {
  type : packet (decodep ContentType) ;
  length : packet (fun x => decodep uint16 x && (S41.bytes2nat x <= length_max)%nat) ;
  fragment : packet (decodep (opaque \[[ (S41.bytes2Z length) \]]))
}.
End S622.

(** **** 6.2.3.1 Null or Standard Stream Cipher *)
Module S6231.
Definition GenericStreamCipher TLSCompressed_length mac_length :=
   struct{ ("content", opaque \[[ TLSCompressed_length \]]) ;
           ("MAC",     opaque \[[ mac_length \]]) }.
End S6231.

(** **** 6.2.3.2 CBC Block Cipher *)
Module S6232.
Import S44.
Definition GenericBlockCipher record_iv_length TLSCompressed_length mac_length padding_length :=
  struct{ ("IV",            opaque \[[ record_iv_length \]]) ;
          ("blockciphered", struct{ ("content",        opaque \[[ TLSCompressed_length \]]) ;
                                    ("MAC",            opaque \[[ mac_length \]]) ;
                                    ("padding",        uint8 \[[ padding_length (*NB: this is supposed to be the value of the next field*) \]]) ;
                                    ("padding_length", uint8) }) }.
End S6232.

(** **** 6.2.3.3 AEAD Ciphers *)
Module S6233.
Definition GenericAEADCipher record_iv_length TLSCompressed_length :=
   struct{ ("nonce_explicit", opaque \[[ record_iv_length \]]) ;
           ("aead-ciphered",  struct{ ("content", opaque \[[ TLSCompressed_length \]]) } ) }.
End S6233.

(** *** 6.2.3 Record Payload Protection *)
Module S623.
Import S621 S44 S61 S6231 S6232 S6233.

Local Open Scope select_scope.

Definition TLSCipherText n (Hn : decodep CipherType n) TLSCompressed_length mac_length record_iv_length padding_length := struct{
  ("type", ContentType) ;
  ("version",  ProtocolVersion) ;
  ("length", uint16) ;
  ("fragment", unpack (select( _ \: _ \: Hn \) \{
        (u2Zc stream, pack (GenericStreamCipher TLSCompressed_length mac_length)) ;
        (u2Zc block, pack (GenericBlockCipher record_iv_length TLSCompressed_length mac_length padding_length)) ;
        (u2Zc aead, pack (GenericAEADCipher record_iv_length TLSCompressed_length))
      \}))
}.

Local Close Scope select_scope.

End S623.

(** * 7. The TLS Handshaking Protocols *)

(** **** 7.4.1.1 Hello Request *)
Module S7411.
Definition HelloRequest := struct{}.
Definition HelloRequestp := decodep HelloRequest.
Definition HelloRequest_packet := packet HelloRequestp.
End S7411.

(** **** 7.4.1.4 Hello Extensions *)
(* NB: we put Section 7.4.1.4 before Section 7.4.1.2  *)
Module S7414.
Definition signature_algorithms := `( 13 )c_8.
Definition ExtensionType :=
  \enum 2 \{ [:: signature_algorithms] \} 65535.
(** The RFC actually defines:
<<
Definition extension_data_type := opaque \< 0 \.. (2^16 - 1) \> 2.
>>
but this is not compatible with "extensions_type" in 7.4.1.2.
*)
Definition extension_data_type :=
  opaque `< 0 \.. 2 ^ 16 - 1 - 2 `> 2.
Definition Extension :=
  struct{ ("extension_type", ExtensionType) ;
          ("extension_data", extension_data_type) }.
End S7414.

(** **** 7.4.1.2 Client Hello *)
Module S7412.
Import S44.
Definition Random :=
  struct{ ("gmt_unix_time", uint32) ;
          ("random_bytes", opaque \[ 28 \])}.
Definition SessionID := opaque `< 0 \.. 32 `> 1.
Definition CipherSuite := uint8 \[ 2 \].

Notation "'NewCipherSuite' l" := (Build_packet (decodep S7412.CipherSuite) l (Logic.eq_refl _)) (at level 9).
Definition CipherSuitePacket := packet (decodep S7412.CipherSuite).

(** NB: CompressionMethod already defined in Sect. 6.1 *)
Definition cipher_suites_type := CipherSuite `< 2 \.. (2 ^ 16 - 2) `> 2.
Import S61.
Definition compression_methods_type := CompressionMethod `< 1 \.. (2 ^ 8 - 1) `> 1.
Import S7414.
Definition extensions_type := Extension `< 0 \.. (2 ^ 16 - 1) `> 2.
Eval compute in (fixed_sz SessionID +
  fixed_sz cipher_suites_type +
  fixed_sz compression_methods_type).
Import S621.
Eval compute in (fixed_sz ProtocolVersion).
Eval compute in (fixed_sz Random).
Definition Hello_sz sid :=
  fixed_sz ProtocolVersion + fixed_sz Random +
  fixed_sz SessionID + Z<=nat sid.
Definition ClientHello_sz sid cys cpm :=
  Hello_sz sid +
  fixed_sz cipher_suites_type + Z<=nat cys +
  fixed_sz compression_methods_type + Z<=nat cpm.
Definition client_extensions_present m sid cys cpm :=
  ClientHello_sz sid cys cpm <? Z<=nat m.

Local Open Scope select_scope.

(** ClientHello parametrized by the length encoded in the outer Handshake packet (type uint24) *)
Structure ClientHello_packet {m} (H : decodep uint24 m) := {
  client_version : packet (fun x => decodep ProtocolVersion x && proverp x) ;
  random : packet (decodep Random) ;
  session_id : packet (decodep SessionID) ;
  cipher_suites : packet (decodep cipher_suites_type) ;
  compression_methods : packet (decodep compression_methods_type) ;
  extensions : packet (
    dselectb( client_extensions_present (nat<=i8 m)
               (var_sz session_id)
               (var_sz cipher_suites)
               (var_sz compression_methods) \)  \{
      (false, decodep struct{}) ;
      (true, decodep extensions_type) \}) }.
Arguments client_version [m H] _.
Arguments random [m H] _.
Arguments session_id [m H] _.
Arguments cipher_suites [m H] _.
Arguments compression_methods [m H] _.
Arguments extensions [m H] _.

Local Close Scope select_scope.

Definition ClientHello_decode m l : bool * seq byte :=
if ~~ decodep uint24 m then (false, l) else
let (a1, l1) := let (a1', l1) := decode ProtocolVersion l in
                (a1' && proverp (take ('|(fixed_sz ProtocolVersion)|) l), l1) in
let (a2, l2) := decode Random l1 in
let (a3, l3) := decode SessionID l2 in
let (a4, l4) := decode cipher_suites_type l3 in
let (a5, l5) := decode compression_methods_type l4 in
if client_extensions_present (nat<=i8 m)
    (size l2 - size l3 - '|(fixed_sz SessionID)|)
    (size l3 - size l4 - '|(fixed_sz cipher_suites_type)|)
    (size l4 - size l5 - '|(fixed_sz compression_methods_type)|) then
  let (a6, l6) := decode extensions_type l5 in
  ([&& a1, a2, a3, a4, a5 & a6], l6)
else
  ([&& a1, a2, a3, a4 & a5], l5).

Definition ClientHellop m l : bool :=
  let (a, l') := ClientHello_decode m l in (a && (size l' == O)).

Lemma ClientHello_packet_ClientHellop m (Hm : decodep uint24 m) : forall (buf : ClientHello_packet Hm),
  ClientHellop m
  (client_version buf ++ random buf ++ session_id buf ++
   cipher_suites buf ++ compression_methods buf ++ extensions buf).
Proof.
case=> /=.
move=> [client_version0 H1] [random0 H2] [session_id0 H3] [cipher_suites0 H4]
  [compression_methods0 H5] [extensions0 H6] /=.
rewrite /ClientHellop /ClientHello_decode.
case :ifP => [Hn' | _].
  by rewrite Hm in Hn'.

move: H1.
rewrite {1}/decodep.
move Hdec_ver : (decode _ _) => dec_ver.
destruct dec_ver as [ret buf].
case/andP.
case/andP.
destruct ret => //= _.
destruct buf => //= _.
rewrite (decode_app _ _ _ _ _ _ Hdec_ver).
rewrite /=.
set tmp := take _ _.
have ->  : proverp tmp = proverp client_version0.
  rewrite /tmp.
  by destruct client_version0 as [|h [|]].
move=> -> /=.

move: H2.
rewrite {1}/decodep.
move Hdec_ran : (decode _ _) => dec_ran.
destruct dec_ran as [ret buf].
case/andP.
destruct ret => //= _.
destruct buf => //= _.
rewrite (decode_app _ _ _ _ _ _ Hdec_ran).

move Hdec_sid : (decode SessionID session_id0) => dec_sid.
destruct dec_sid as [ret buf].
rewrite /=.
destruct ret in Hdec_sid; last first.
  clear H6.
  by rewrite /decodep Hdec_sid in H3.
destruct buf in Hdec_sid; last first.
  clear H6.
  by rewrite /decodep Hdec_sid in H3.
rewrite (decode_app _ _ _ _ _ _ Hdec_sid).

move Hdec_cyp : (decode cipher_suites_type cipher_suites0) => dec_cyp.
destruct dec_cyp as [ret buf].
destruct ret in Hdec_cyp; last first.
  clear H6.
  by rewrite /decodep Hdec_cyp in H4.
destruct buf in Hdec_cyp; last first.
  clear H6.
  by rewrite /decodep Hdec_cyp in H4.
rewrite (decode_app _ _ _ _ _ _ Hdec_cyp).

move Hdec_cmp : (decode compression_methods_type compression_methods0) => dec_cmp.
destruct dec_cmp as [ret buf].
destruct ret in Hdec_cmp; last first.
  clear H6.
  by rewrite /decodep Hdec_cmp in H5.
destruct buf in Hdec_cmp; last first.
  clear H6.
  by rewrite /decodep Hdec_cmp in H5.
rewrite (decode_app _ _ _ _ _ _ Hdec_cmp).

move: H6 => /=.
move Htest : (client_extensions_present _ _ _ _) => [] /=.
- (* extensions present *) move=> H7.
  case: ifP.
  + move=> H8.
    rewrite -(cats0 extensions0).
    move: H7.
    rewrite {1}/decodep.
    move Hdec_ext : (decode _ _) => dec_ext.
    destruct dec_ext as [ret buf].
    case/andP.
    destruct ret => //= _.
    destruct buf => //= _.

    rewrite /= in Htest.
    by rewrite (decode_app _ _ _ _ _ _ Hdec_ext).
  + move=> H8.
    have X1 : (size
            (session_id0 ++
             cipher_suites0 ++ compression_methods0 ++ extensions0) -
            size
            (cipher_suites0 ++ compression_methods0 ++ extensions0))%nat = size session_id0.
      by rewrite !size_cat /= -addnBA // subnn addn0.
    rewrite X1 in H8.
    have X2 : (size (cipher_suites0 ++ compression_methods0 ++ extensions0) -
            size
            (compression_methods0 ++ extensions0))%nat = size cipher_suites0.
      by rewrite size_cat -addnBA // subnn addn0.
    rewrite X2 in H8.
    have X3 : (size (compression_methods0 ++ extensions0) -
          size extensions0)%nat = size compression_methods0.
      by rewrite size_cat -addnBA // subnn addn0.
    rewrite X3 in H8.
    exfalso.
    move: Htest H8.
    by move=> ->.
- move=> H7.
  destruct extensions0 => //=.
  move: Htest.
  have -> : (size
               (session_id0 ++ cipher_suites0 ++ compression_methods0 ++ nil) -
             size (cipher_suites0 ++ compression_methods0 ++ nil))%nat = size session_id0.
    by rewrite size_cat -addnBA // subnn addn0.
  have -> : (size (cipher_suites0 ++ compression_methods0 ++ nil) -
             size (compression_methods0 ++ nil))%nat = size cipher_suites0.
    by rewrite size_cat -addnBA // subnn addn0.
  rewrite subn0 cats0.
  by move=> ->.
Qed.

End S7412.

(** **** 7.4.1.3 Server Hello *)
Module S7413.
Import S621 S7412 S61 S44.
Definition ServerHello_sz (sid : nat) :=
  Hello_sz sid + fixed_sz CipherSuite + fixed_sz CompressionMethod.
Definition server_extensions_present n (fld1 : nat) :=
  ServerHello_sz fld1 <? Z<=nat n.

Local Open Scope select_scope.

(* NB: the length that is embedded in the handshake packet? *)
Structure ServerHello_packet {n} (Hn : decodep uint24 n) := {
  server_version : packet (decodep ProtocolVersion) ;
  random : packet (decodep Random) ;
  session_id : packet (decodep SessionID) ;
  cipher_suite : packet (decodep CipherSuite) ;
  compression_method : packet (decodep CompressionMethod) ;
  extensions : packet (dselectb( (server_extensions_present (nat<=i8 n) (size session_id)) \) \{
        (false, decodep struct{} ) ;
        (true, decodep extensions_type)
      \})
}.

Local Close Scope select_scope.

(* NB : on the model of ClientHellop, no need to pass n/Hn parameters,
   the server_extensions_present can be decided from the list of bytes *)
Axiom ServerHellop : forall {n}, decodep uint24 n -> seq byte -> bool.
End S7413.

(** *** 7.4.2 Server Certificate *)
Module S742.
Definition ASN1Cert := opaque `< 1 \.. 2^24 - 1 `> 3.
Definition certificate_list_type := ASN1Cert `< 0 \.. 2^24 - 1 `> 3.
Definition Certificate := struct{
  ("certificate_list", certificate_list_type)
}.
Definition Certificatep := decodep Certificate.
End S742.

(** *** 7.4.3 Server Key Exchange Message *)
Module S743.
Definition dhe_dss := `( 0 )c_8. Definition dhe_rsa := `( 1 )c_8. Definition dh_anon := `( 2 )c_8.
Definition rsa := `( 3 )c_8. Definition dh_dss := `( 4 )c_8. Definition dh_rsa := `( 5 )c_8.
Definition KeyExchangeAlgorithm := \enum 1 \{ dhe_dss :: dhe_rsa :: dh_anon ::
  rsa :: dh_dss :: dh_rsa :: nil \}.
Definition dh_p_type := opaque `< 1 \.. 2 ^ 16 - 1 `> 2.
Definition dh_g_type := opaque `< 1 \.. 2 ^ 16 - 1 `> 2.
Definition dh_Ys := opaque `< 1 \.. 2 ^ 16 - 1 `> 2.
Definition ServerDHParams :=
   struct{ ("dh_p", dh_p_type) ;
           ("dh_g", dh_g_type) ;
           ("dh_Ys", dh_Ys) }.
Definition dhe_dss_rsa_type := struct{
  ("params", ServerDHParams) ;
  ("signed_params", struct{
    ("client_random", opaque \[ 32 \]) ;
    ("server_random", opaque \[ 32 \]) ;
    ("params", ServerDHParams)
  }) }.

Local Open Scope select_scope.

Definition ServerKeyExchange {n} (Hn : decodep KeyExchangeAlgorithm n) := struct{
  ("params", unpack (select( _ \: _ \: Hn\) \{
    (u2Zc dhe_dss, pack dhe_dss_rsa_type) ;
    (u2Zc dhe_rsa, pack dhe_dss_rsa_type) ;
    (u2Zc dh_anon, pack ServerDHParams) ;
    (u2Zc rsa, pack struct{}) ;
    (u2Zc dh_dss, pack struct{}) ;
    (u2Zc dh_rsa, pack struct{})
  \}))
}.

Local Close Scope select_scope.

Definition ServerKeyExchangep {n} (Hn : decodep KeyExchangeAlgorithm n) :=
  decodep (ServerKeyExchange Hn).
End S743.

(** *** 7.4.4 Certificate Request *)
Module S744.
Import S74141.
Definition DistinguishedName := opaque `< 1 \.. 2 ^ 16 - 1 `> 2.
Definition rsa_sign := `( 1 )c_8. Definition dss_sign := `( 2 )c_8. Definition rsa_fixed_dh := `( 3 )c_8.
Definition dss_fixed_dh := `( 4 )c_8. Definition rsa_ephemeral_dh_RESERVED := `( 5 )c_8.
Definition dss_ephemeral_dh_RESERVED := `( 6 )c_8. Definition fortezza_dms_RESERVED := `( 20 )c_8.
Definition ClientCertificateType := \enum 1 \{ rsa_sign :: dss_sign :: rsa_fixed_dh ::
  dss_fixed_dh :: rsa_ephemeral_dh_RESERVED :: dss_ephemeral_dh_RESERVED ::
  fortezza_dms_RESERVED :: nil \} 255.
Definition CertificateRequest := struct{
  ("certificate_types", ClientCertificateType `< 1 \.. 2 ^ 8 - 1 `> 1) ;
  ("supported_signature_algorithms", SignatureAndHashAlgorithm `< 0 \.. 2 ^ 16 - 1 `> 2) ; (* NB: error, the RFC forgot the min *)
  ("certificate_authorities", DistinguishedName `< 0 \.. 2 ^ 16 - 1 `> 2)
}.
Definition CertificateRequestp := decodep CertificateRequest.
End S744.

(** *** 7.4.5 Server Hello Done *)
Module S745.
Definition ServerHelloDone := struct{}.
Definition ServerHelloDonep := decodep ServerHelloDone.
End S745.

(** **** 7.4.7.1 RSA-Encrypted Premaster Secret Message *)

Module S7471.
Import S621.
Definition PreMasterSecret := struct{
  ("client_version", ProtocolVersion) ;
  ("random", opaque \[ 46 \]) }.
Definition EncryptedPreMasterSecret := struct{
  ("pre_master_secret", PreMasterSecret) }.
End S7471.

(** **** 7.4.7.2 Client Diffie-Hellman Public Value *)

Module S7472.
Definition implicit := `( 0 )c_8. Definition explicit := `( 1 )c_8.
Definition PublicValueEncoding := \enum 1 \{ implicit :: explicit :: nil \}.
(* NB: dh_public is also called dh_Yc *)

Local Open Scope select_scope.

Definition ClientDiffieHellmanPublic {n} (Hn : decodep PublicValueEncoding n) := struct{
  ("dh_public", unpack (select( _ \: _ \: Hn \) \{
    (u2Zc implicit, pack struct{}) ;
    (u2Zc explicit, pack (opaque `< 1 \.. 2 ^ 16 - 1 `> 2))
    \}))
  }.

Local Close Scope select_scope.

End S7472.

(** *** 7.4.7 Client Key Exchange Message *)

Module S747.
Import S743 S7471 S7472.

Local Open Scope select_scope.

Definition ClientKeyExchange {n} (Hn : decodep KeyExchangeAlgorithm n) {m} (Hm : decodep PublicValueEncoding m) :=
struct{
  ("exchange_keys", unpack (select( _ \: _ \: Hn\) \{
    (u2Zc dhe_dss, pack (ClientDiffieHellmanPublic Hm)) ;
    (u2Zc dhe_rsa, pack (ClientDiffieHellmanPublic Hm)) ;
    (u2Zc dh_anon, pack (ClientDiffieHellmanPublic Hm)) ;
    (u2Zc rsa, pack EncryptedPreMasterSecret) ;
    (u2Zc dh_dss, pack (ClientDiffieHellmanPublic Hm)) ;
    (u2Zc dh_rsa, pack (ClientDiffieHellmanPublic Hm))
  \}))
}.

Local Close Scope select_scope.

Definition ClientKeyExchangep {n} (Hn : decodep KeyExchangeAlgorithm n) {m} (Hm : decodep PublicValueEncoding m) :=
  decodep (ClientKeyExchange Hn Hm).
End S747.

(** *** 7.4.8 Certificate Verify *)
Module S748.
Definition CertificateVerify (handshake_messages_length : Z) := struct{
  ("handshake_messages", opaque \[[ handshake_messages_length \]])
}.
Definition CertificateVerifyp (handshake_messages_length : Z) :=
  decodep (CertificateVerify handshake_messages_length).
End S748.

(** *** 7.4.9 Finished *)
Module S749.
Definition verify_data_lengthp x := 12 <= x.
Definition verify_data_type (verify_data_length : Z(*NB:depends on the cipher suite*)) :=
  opaque \[[ verify_data_length \]].
Definition Finished (verify_data_length : Z) := struct{ ("verify_data", verify_data_type verify_data_length) }.
Definition Finishedp (verify_data_length : Z) := decodep (Finished verify_data_length).
Definition Finished_packet (x : Z) := packet (Finishedp x).
End S749.

(** ** 7.4 Handshake Protocol *)
Module S74.
Definition hello_request := `( 0 )c_8.
Definition client_hello := `( 1 )c_8.
Definition server_hello := `( 2 )c_8.
Definition certificate := `( 11 )c_8.
Definition server_key_exchange := `( 12 )c_8.
Definition certificate_request := `( 13 )c_8.
Definition server_hello_done := `( 14 )c_8.
Definition certificate_verify := `( 15 )c_8.
Definition client_key_exchange := `( 16 )c_8.
Definition finished := `( 20 )c_8.
Definition HandshakeType := \enum 1 \{ hello_request :: client_hello ::
  server_hello :: certificate :: server_key_exchange :: certificate_request ::
  server_hello_done :: certificate_verify :: client_key_exchange ::
  finished :: nil \} 255.
Import S44 S7411 S7412 S7413 S742 S743 S744 S745 S747 S748 S749 S7472.

Local Open Scope select_scope.

Definition Handshake_packet_helper {n} (Hn : decodep KeyExchangeAlgorithm n)
  {m} (Hm : decodep PublicValueEncoding m) (verify_data_length handshake_messages_length : Z)
  (length : packet (decodep uint24)) (msg_type : packet (decodep HandshakeType)) (x : seq byte) :=
    (dselect( _ \: _ \: decodable _ msg_type \) \{
        (u2Zc hello_request, HelloRequestp) ;
        (u2Zc client_hello, ClientHellop length (*(decodable _ length)*)) ;
        (u2Zc server_hello, ServerHellop (decodable _ length)) ;
        (u2Zc certificate, Certificatep) ;
        (u2Zc server_key_exchange, ServerKeyExchangep Hn) ;
        (u2Zc certificate_request, CertificateRequestp) ;
        (u2Zc server_hello_done, ServerHelloDonep) ;
        (u2Zc certificate_verify, CertificateVerifyp handshake_messages_length) ;
        (u2Zc client_key_exchange, ClientKeyExchangep Hn Hm) ;
        (u2Zc finished, Finishedp handshake_messages_length)
      \}) x && (size x == nat<=i8 n).

Local Close Scope select_scope.

Structure Handshake_packet {n} (Hn : decodep KeyExchangeAlgorithm n) {m} (Hm : decodep PublicValueEncoding m)
  (verify_data_length handshake_messages_length : Z) := {
  msg_type : packet (decodep HandshakeType) ;
  length : packet (decodep uint24) ;
  body : packet (Handshake_packet_helper Hn Hm verify_data_length handshake_messages_length
    length msg_type)
}.

Definition Handshake_header_decode l : bool * seq byte * seq byte :=
  let (a1, l1) := decode HandshakeType l in
  let (a2, l2) := decode uint24 l1 in
  (a1 && a2, take ('|(fixed_sz uint24)|) l1, l2).

Definition Handshake_hd := fixed_sz HandshakeType + fixed_sz uint24.
End S74.

Module A5.

Import S7412.

(**      CipherSuite TLS_NULL_WITH_NULL_NULL               = { 0x00,0x00 };*)
Definition TLS_NULL_WITH_NULL_NULL : CipherSuitePacket := NewCipherSuite [:: \0x"00" ; \0x"00"].

Definition TLS_RSA_WITH_NULL_MD5 := NewCipherSuite [:: \0x"00" ; \0x"01"].
Definition TLS_RSA_WITH_NULL_SHA := NewCipherSuite [:: \0x"00" ; \0x"02"].
Definition TLS_RSA_WITH_NULL_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"3B"].
Definition TLS_RSA_WITH_RC4_128_MD5 := NewCipherSuite [:: \0x"00" ; \0x"04"].
Definition TLS_RSA_WITH_RC4_128_SHA := NewCipherSuite [:: \0x"00" ; \0x"05"].
Definition TLS_RSA_WITH_3DES_EDE_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"0A"].
Definition TLS_RSA_WITH_AES_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"2F"].
Definition TLS_RSA_WITH_AES_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"35"].
Definition TLS_RSA_WITH_AES_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"3C"].
Definition TLS_RSA_WITH_AES_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"3D"].
Definition TLS_DH_DSS_WITH_3DES_EDE_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"0D"].
Definition TLS_DH_RSA_WITH_3DES_EDE_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"10"].
Definition TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"13"].
Definition TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"16"].
Definition TLS_DH_DSS_WITH_AES_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"30"].
Definition TLS_DH_RSA_WITH_AES_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"31"].
Definition TLS_DHE_DSS_WITH_AES_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"32"].
Definition TLS_DHE_RSA_WITH_AES_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"33"].
Definition TLS_DH_DSS_WITH_AES_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"36"].
Definition TLS_DH_RSA_WITH_AES_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"37"].
Definition TLS_DHE_DSS_WITH_AES_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"38"].
Definition TLS_DHE_RSA_WITH_AES_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"39"].
Definition TLS_DH_DSS_WITH_AES_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"3E"].
Definition TLS_DH_RSA_WITH_AES_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"3F"].
Definition TLS_DHE_DSS_WITH_AES_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"40"].
Definition TLS_DHE_RSA_WITH_AES_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"67"].
Definition TLS_DH_DSS_WITH_AES_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"68"].
Definition TLS_DH_RSA_WITH_AES_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"69"].
Definition TLS_DHE_DSS_WITH_AES_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"6A"].
Definition TLS_DHE_RSA_WITH_AES_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"6B"].
Definition TLS_DH_anon_WITH_RC4_128_MD5 := NewCipherSuite [:: \0x"00" ; \0x"18"].
Definition TLS_DH_anon_WITH_3DES_EDE_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"1B"].
Definition TLS_DH_anon_WITH_AES_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"34"].
Definition TLS_DH_anon_WITH_AES_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"3A"].
Definition TLS_DH_anon_WITH_AES_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"6C"].
Definition TLS_DH_anon_WITH_AES_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"6D"].

End A5.

End RFC5246.

(** Camellia Cipher Suites for TLS *)

Module RFC5932.

Import RFC5246.
Export RFC5246.

Import S7412.

Definition TLS_RSA_WITH_CAMELLIA_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"41"].
Definition TLS_DH_DSS_WITH_CAMELLIA_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"42"].
Definition TLS_DH_RSA_WITH_CAMELLIA_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"43"].
Definition TLS_DHE_DSS_WITH_CAMELLIA_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"44"].
Definition TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"45"].
Definition TLS_DH_anon_WITH_CAMELLIA_128_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"46"].

Definition TLS_RSA_WITH_CAMELLIA_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"84"].
Definition TLS_DH_DSS_WITH_CAMELLIA_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"85"].
Definition TLS_DH_RSA_WITH_CAMELLIA_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"86"].
Definition TLS_DHE_DSS_WITH_CAMELLIA_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"87"].
Definition TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"88"].
Definition TLS_DH_anon_WITH_CAMELLIA_256_CBC_SHA := NewCipherSuite [:: \0x"00" ; \0x"89"].

Definition TLS_RSA_WITH_CAMELLIA_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"BA"].
Definition TLS_DH_DSS_WITH_CAMELLIA_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"BB"].
Definition TLS_DH_RSA_WITH_CAMELLIA_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"BC"].
Definition TLS_DHE_DSS_WITH_CAMELLIA_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"BD"].
Definition TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"BE"].
Definition TLS_DH_anon_WITH_CAMELLIA_128_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"BF"].

Definition TLS_RSA_WITH_CAMELLIA_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"C0"].
Definition TLS_DH_DSS_WITH_CAMELLIA_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"C1"].
Definition TLS_DH_RSA_WITH_CAMELLIA_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"C2"].
Definition TLS_DHE_DSS_WITH_CAMELLIA_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"C3"].
Definition TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"C4"].
Definition TLS_DH_anon_WITH_CAMELLIA_256_CBC_SHA256 := NewCipherSuite [:: \0x"00" ; \0x"C5"].

End RFC5932.

(** Technical Lemmas *)

Module RFC5246_Prop.

Import RFC5246.

Lemma decode_SessionID : forall s h, nat<=u h = size s ->
  decode S7412.SessionID (h :: s) = (true, nil).
Proof.
move=> s h hs.
rewrite /decode /= take0 drop0.
have Htmp : (nat<=u h = nat<=i8 (h :: nil))%nat.
  by rewrite /(nat<=i8) /MachineIntByte_m.bytes2nat /bSum_c /= -u2ZE -/(nat<=u h) hs.
rewrite -{}Htmp {}hs leqnn take_size drop_size.
set f := fun _ _ => _.
suff : foldl f (true, s) (nseq (size s) tt) = (true, nil) by move=> ->.
by elim: s.
Qed.

Lemma decode_cipher_suites_type : forall s h1 h2,
  nat<=i8 (h1 :: h2 :: nil) = size s -> ~~ odd (size s) ->
  decode S7412.cipher_suites_type (h1 :: h2 :: s) = (true, nil).
Proof.
move=> s h1 h2 hs Hodd.
have {Hodd}[k Hk] : exists k, size s = k.*2.
  exists (size s)./2.
  rewrite -{1}(odd_double_half (size s)).
  by destruct (odd (size s)).
rewrite /decode /= take0 drop0 hs leqnn take_size drop_size {hs}.
set f := fun _ _ => _.
suff : foldl f (true, s) (nseq (size s) tt) = (true, nil) by move=> ->.
have : foldl f (true, s) (nseq k tt) = (true, nil).
  elim: k s Hk => [| k IHk [|s1 [|s2 s3]]] //.
    by destruct s.
  rewrite doubleS [size _]/=.
  case=> H.
  rewrite /f [Z<=nat]lock /= -lock drop0 ifT; last first.
    by apply/leZP; rewrite 2!Z_S; omega.
  by apply IHk.
rewrite Hk.
move Htmp : k.*2 => k'.
have {Htmp}k'k : (k <= k')%nat by rewrite -Htmp -{1}(muln1 k) -muln2; apply leq_mul.
elim: k' k k'k s Hk => [| k' IHk' [|k] // kk' s]; first by case.
  destruct s => //; by apply IHk'.
destruct s as [|s1 [|s2 s3]] => //.
rewrite doubleS [size _]/=.
case => Hs.
rewrite /f [Z<=nat]lock /= -lock ifT; last first.
  apply/leZP; rewrite 2!Z_S; omega.
rewrite drop0; by apply IHk'.
Qed.

Lemma decode_compression_methods_type : forall h n, n = nat<=u h ->
  decode S7412.compression_methods_type (h :: nseq n `( 0 )_8) = (true, nil).
Proof.
move=> h n nh.
rewrite /decode /= take0 drop0 size_nseq.
have Htmp : (nat<=u h = nat<=i8 (h :: nil))%nat.
  by rewrite /(nat<=i8) /MachineIntByte_m.bytes2nat /bSum_c /= -u2ZE.
rewrite -{}Htmp -nh leqnn drop_nseq // subnn /=.
set f := fun _ _ => _.
rewrite {1}(_ : n = size (nseq n `( 0 )_8)); last by rewrite size_nseq.
rewrite take_size {nh}.
move Hs : (nseq _ _) => s.
suff : foldl f (true, s) (nseq n tt) = (true, nil) by rewrite -{}Hs; move=> ->.
elim: s n Hs => [|hd tl IH [|n0] //= [H1 H2]].
  by case.
rewrite drop0 take0 inE -H1 /S41.bytes2Z /= /MachineIntByte_m.bytes2Z /bSum_c /= -u2ZE Z2uK // eqxx.
by apply IH.
Qed.

Lemma size_CipherSuitePacket (p : S7412.CipherSuitePacket) : size p = 2%nat.
Proof.
destruct p as [ [| b [|b0 [|b1 body0]]] decodable0] => //=.
rewrite /decodep /= /decode /= in decodable0.
by case: ifP decodable0.
Qed.

End RFC5246_Prop.

Module test.

Import RFC5932.

Goal (decode opaque (nseq 1 `( 100 )c_8)) = (true, nil).
Proof. by rewrite /decode /=. Qed.

Goal (decode (opaque \[ 3 \]) (nseq 3 `( 100 )c_8)) = (true, nil).
Proof. by rewrite /decode /=. Qed.

Goal decodep S45.Color (S45.white :: nil) = true.
Proof. by []. Qed.

Goal decodep S45.Color (`( 4 )c_8 :: nil) = false.
Proof. by []. Qed.

Local Open Scope select_scope.

Goal (select( (S461.apple :: nil) \: S461.VariantTag \: Logic.eq_refl \) \{
  (u2Zc S461.apple, pack S461.V1) ;
  (u2Zc S461.orange, pack S461.V2) ;
  (u2Zc S461.banana, pack S461.V2)
  \} ) = pack S461.V1.
Proof. done. Qed.

Local Close Scope select_scope.

Goal decode S7412.SessionID (`( 3 )c_8 :: nseq 4 `( 100 )c_8) = (true, `( 100 )c_8 :: nil).
Proof. done. Qed.

Goal decodep S7412.SessionID (`( 3 )c_8:: nseq 3 `( 100 )c_8) = true.
Proof. done. Qed.

Goal decode S7412.cipher_suites_type (map (fun x => `( x )c_8) (0 :: 4 :: 1::2 :: 3::4 :: nil)) = (true, nil).
(*                                          |--| 2nd CipherSuite
                                    |--| 1st CipherSuite
                            |--| length of cipher_suites = 4bytes = 2CipherSuite

*)
Proof. by rewrite /decode /=. Qed.

Goal \0x "2A"%string = `( 42 )c_8.
apply u2Z_inj.
by rewrite /MachineIntByte_m.hex2t /= -!Z2uE (@u2Z_concat 4) /= !u2ZE !Z2uE.
Qed.

Goal \0x "F3"%string = `( 243 )c_8.
apply u2Z_inj.
by rewrite /MachineIntByte_m.hex2t /= -!Z2uE (@u2Z_concat 4) /= !u2ZE !Z2uE.
Qed.

(*Goal \0x "2AF3"%string = 10995. done. Qed.*)

End test.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrnat_ext Coq.Program.Wf.
Require Import ssrZ ZArith_ext String_ext Ascii PArith.
Require Import machine_int.
Import MachineInt.

Require Import
  C_types C_types_fp C_value C_expr C_expr_equiv C_expr_ground C_seplog C_tactics.

Local Open Scope C_expr_scope.
Local Open Scope C_types_scope.
Local Open Scope zarith_ext_scope.

Definition newline := String "010" ""%string.
Definition line s := (s ++ newline)%string.

Definition pp_Ndigit (n : N) (tl : string) : string :=
  if N.leb n 9
    then String (Ascii.ascii_of_N (n + Ascii.N_of_ascii "0"%char)) tl
    else tl.

Lemma nat_of_posE : forall p, nat_of_pos p = Pos.to_nat p.
Proof.
  let s := eval lazy in (String "254" "" ++ "test" ++ String "255" "")%string in idtac s.
  elim=> //= p IHp.
  - by rewrite Pos2Nat.inj_xI -/muln_rec -mulnE IHp NatTrec.doubleE mul2n.
  - by rewrite Pos2Nat.inj_xO -/muln_rec -mulnE IHp NatTrec.doubleE mul2n.
Qed.

(*Obligation Tactic := Tactics.program_simpl.*)

Program Fixpoint pp_positive
  (p : positive) (tl : string) {measure (Pos.to_nat p)} : string :=
  let: (rd, rm) := N.pos_div_eucl p 10 in
  match rd with
    | N0 => pp_Ndigit rm tl
    | Npos a => pp_positive a (pp_Ndigit rm tl)
  end.
Next Obligation.
  apply /ltP.
  move: (N.pos_div_eucl_spec p 10).
  rewrite -{}Heq_anonymous -!positive_N_nat => ->.
  rewrite Nnat.N2Nat.inj_add Nnat.N2Nat.inj_mul /= plusE multE.
  apply ltn_addr.
  rewrite -{1}(muln1 (Pos.to_nat a)) ltn_mul2l.
  apply/andP; split => //; apply/ltP; apply Pos2Nat.is_pos.
Qed.

Eval compute in (N.pos_div_eucl 123456789 10).
Eval lazy in (pp_positive 123456789 "").

Definition pp_Z (z : Z) (tl : string) : string :=
  match z with
    | Zpos p => pp_positive p tl
    | Z0     => "0" ++ tl
    | Zneg p => "-" ++ (pp_positive p tl)
  end%string.

Definition pp_N (n : N) (tl : string) : string :=
  match n with
    | Npos p => pp_positive p tl
    | N0 => "0" ++ tl
  end%string.

Definition pp_nat (n : nat) (tl : string) : string := pp_N (bin_of_nat n) tl.

Definition pp_var (v : string_eqType) (tl : string) : string :=
  (v ++ tl)%string.

Definition pp_uint {n : nat} (i : int n) (tl : string) : string :=
  pp_Z (u2Z i) tl.

Definition pp_sint {n : nat} (i : int n) (tl : string) : string :=
  pp_Z (s2Z i) tl.

Definition pp_binop_ne (op : binop_ne) (tl : string) : string :=
  (match op with
     | add_e => "+"
     | sub_e => "-"
     | mul_e => "*"
     | and_e => "&"
     | or_e  => "|"
     | shl_e => "<<"
  end ++ tl)%string.

Definition pp_binop_re (op : binop_re) (tl : string) : string :=
  (match op with
     | le_e   => "<="
     | lt_e   => "<"
     | gt_e   => ">"
     | ge_e   => ">="
     | land_e => "&&"
     | lor_e  => "||"
     | eq_e   => "=="
     | neq_e  => "!="
  end ++ tl)%string.

Definition pp_binopk_e (op : binopk_e) (tl : string) : string :=
  (match op with
     | mod2n_e => "%"
   end ++ tl)%string.

Definition integral_to_string (t : integral) (tl : string) : string :=
  (match t with
     | uint  => "unsigned int"
     | sint  => "int"
     | uchar => "unsigned char"
     | schar => "signed char"
     | ulong => "unsigned long"
   end ++ tl)%string.

Definition struct_tag_to_string (tag : tag) (tl : string) : string :=
  let: mkTag s := tag in (s ++ tl)%string.

Fixpoint typ_to_string
  (t : typ) (name : string) (tl : string) {struct t} : string :=
  match t with
    | ityp ty  => integral_to_string ty (" " ++ name ++ tl)
    | ptyp ty  => typ_to_string ty ("(*" ++ name ++ ")") tl
    | styp tag => "struct " ++ struct_tag_to_string tag (" " ++ name ++ tl)
    | atyp sz H tag =>
      "struct " ++
      struct_tag_to_string tag (" " ++ name ++ "[" ++ pp_nat sz ("]" ++ tl))
  end%string.

Eval compute in (typ_to_string (ptyp (ptyp (atyp 10 _ (mkTag "pair")))) "a" "").

Definition typ_to_string_rec
  g (t : g.-typ) (name : string) (tl : string) : string :=
  @typ_traversal
    g (string -> string -> string) string
    (mkConfig g
      (fun t name tl => integral_to_string t (" " ++ name ++ tl))
      (fun t name tl => typ_to_string t ("(*" ++ name ++ ")") tl)
      (fun accu p => accu ++ p.2 p.1.1 ("; "))
      (fun p f name tl => "struct " ++
        struct_tag_to_string p.1 (" { " ++ f "" ++ "} " ++ name ++ tl))
      (fun sz _ f name tl => f name ("[" ++ pp_nat sz ("]" ++ tl))))%string
    t name tl.

Definition phyval_to_string_ityp
    (t : integral) (val : seq (int 8)) (tl : string) : string :=
  (if sizeof_integral t == size val
    then
      let val' := foldl (fun acc x => acc * 256 + u2Z x) 0 val
      in (if is_signed t
        then pp_Z (if 2 ^^ (size val * 8 - 1) <=? val'
                   then val' - 2 ^^ (size val * 8) else val') tl
        else pp_Z val' ("u" ++ tl))
    else "/* ERROR: phyval_to_string_ityp */" ++ tl)%string.

Definition phyval_to_string_ptyp
  (t : typ) (val : seq (int 8)) (tl : string) : string :=
  ((if sizeof_ptr == (size val)
    then
      if foldl (fun acc x => acc * 256 + u2Z x) 0 val is 0
        then "NULL"
        else "/* ERROR: phyval_to_string_ptyp */"
    else "/* ERROR: phyval_to_string_ptyp */") ++ tl)%string.

Fixpoint intercalate (A : Type) (s : A) (xs : seq A) :=
  match xs with
    | nil => nil
    | x :: nil => x :: nil
    | x :: xs => x :: s :: intercalate A s xs
  end.

Definition phyval_to_string
  g (t : g.-typ) : seq (int 8) -> string -> string :=
  typ_traversal g
  (@mkConfig g
    (seq (int 8) -> string -> string)
    (nat * seq string * seq (int 8))
    (fun t val tl => phyval_to_string_ityp t val tl)
    (fun t val tl => phyval_to_string_ptyp t val tl)
    (fun accu p =>
      let: (len, r, val) := accu in
      let padd := padd len (align p.1.2) in
      let esize := sizeof p.1.2 in
      ((len + padd + esize)%nat,
        (p.2 (take esize (drop padd val)) "") :: r,
        drop (padd + esize) val))
    (fun p f val tl =>
      let: (len, r, val') := f (O, Nil string, val) in
      (if size val' == padd len (align p.2)
        then ""
        else "/* ERROR: phyval_to_string (f_styp_fin) */") ++
      "{" ++
      (foldl append "" (intercalate string ", " (rev r))) ++
      "}" ++ tl)%string
    (fun n p f val tl =>
      let: (tg, ty) := p in
      (fix g n val tl :=
        if n is n.+1
          then (let: (vall, valr) := seq_ext.split_n val (sizeof ty) in
                f vall (g n valr tl))
          else tl) n val tl)
  )%string t.

Fixpoint pp_exp
  (g : wfctxt) (sigma : g.-env) (ty : g.-typ)
  (e : @exp g sigma ty) (tl : string) : string :=
  match e with
    | var_e v _ _ => pp_var v tl
    | cst_e ty v => phyval_to_string g ty (phy2seq v) tl
    | bop_n t op el er =>
        "(" ++ pp_exp _ _ _ el (") " ++ pp_binop_ne op
      (" (" ++ pp_exp _ _ _ er (")" ++ tl)))
    | bopk_n t op el n =>
      "(" ++ pp_exp _ _ _ el (") " ++ pp_binopk_e op (" " ++ pp_nat n tl))
    | bop_r t op el er =>
        "(" ++ pp_exp _ _ _ el (") " ++ pp_binop_re op
      (" (" ++ pp_exp _ _ _ er (")" ++ tl)))
    | add_p t el er =>
      "(" ++ pp_exp _ _ _ el (") + (" ++ pp_exp _ _ _ er (")" ++ tl))
    | safe_cast t1 t2 e _ =>
      "(" ++ typ_to_string (ityp t1) ")(" (pp_exp _ _ _ e (")" ++ tl))
    | unsafe_cast t1 t2 e _ =>
      "(" ++ typ_to_string (ityp t1) ")(" (pp_exp _ _ _ e (")" ++ tl))
    | fldp f tg t e _ _ _ =>
      "(" ++ pp_exp _ _ _ e (")->" ++ f ++ tl)
    | eq_p t el er =>
      "(" ++ pp_exp _ _ _ el (") == (" ++ pp_exp _ _ _ er (")" ++ tl))
    | ifte_e t e1 e2 e3 =>
      "(" ++ pp_exp _ _ _ e1 (") ? (" ++ pp_exp _ _ _ e2 (") : " ++
      "(" ++ pp_exp _ _ _ e3 (")" ++ tl)))
  end%string.

Fixpoint pp_bexp
  (g : wfctxt) (sigma : g.-env) (e : @bexp g sigma) (tl :string) : string :=
  match e with
    | exp2bexp e => "(" ++ pp_exp _ _ _ e (")" ++ tl)
    | bneg b => "!(" ++ pp_bexp g sigma b (")" ++ tl)
  end%string.

Module C_Pp_f (C_Env : CENV).

Definition g := C_Env.g.
Definition sigma := C_Env.sigma.

Module Import C_Seplog_m := C_Tactics_f C_Env.
Export C_Seplog_m.

Definition pp_ctxt :=
  (foldl
    (fun s t =>
      s ++
      line ("struct " ++ match t with (mkTag s, _) => s end ++ " {") ++
      (foldl
        (fun s f =>
          s ++ line ("    " ++ typ_to_string (snd f) (fst f) ";"))
        "" (snd t)) ++
      line "};")
    ""
    (topsort_ctxt g))%string.

Definition pp_cmd0 (c : cmd0) (tl : string) :=
  let semicolon := (";" ++ newline)%string in
  match c with
    | skip =>
      semicolon ++ tl
    | assign t x _ e =>
      x ++ " = " ++ pp_exp g sigma t e (semicolon ++ tl)
    | lookup t x _ e =>
      x ++ " = *" ++ pp_exp g sigma (:* t) e (semicolon ++ tl)
    | mutation t el er =>
      "*" ++ pp_exp g sigma (:* t) el
      (" = " ++ pp_exp g sigma t er (semicolon ++ tl))
  end%string.

(*
  pp_cmd':
  pp_cmd:
*)
Fixpoint pp_cmd' (i : nat) (c : cmd) (tl : string) :=
  let pp_indent i := ssrnat.iter i (append "    ") in
  let pp_cmd i c tl := pp_indent i (pp_cmd' i c tl) in
  match c with
    | cmd_cmd0 c0 => pp_cmd0 c0 tl
    | cmd_seq cl cr => pp_cmd' i cl (pp_cmd i cr tl)
    | ifte e cl cr =>
      "if (" ++ pp_bexp g sigma e
      (") {" ++ newline ++ pp_cmd i.+1 cl
      (pp_indent i ("} else {" ++ newline ++ pp_cmd i.+1 cr
      (pp_indent i ("}" ++ newline ++ tl)))))
    | while e c =>
      "while (" ++ pp_bexp g sigma e
      (") {" ++ newline ++ pp_cmd i.+1 c
      (pp_indent i ("}" ++ newline ++ tl)))
  end%string.

Definition pp_cmd (i : nat) (c : cmd) (tl : string) :=
    ssrnat.iter i (append "    ") (pp_cmd' i c tl).

End C_Pp_f.

Require Import ZArith.
Require Import Setoid.

Lemma s2Z_Z2u : forall {n:nat} (z:Z), 0 <= z < 2 ^^ Peano.pred n -> s2Z (Z2u n z) = z.
Proof.
move => n z [H1 H2].
have ? : 0 <= z < 2 ^^ n.
  split => //.
  apply (@ltZ_leZ_trans (2 ^^ predn n)) => //.
  by apply/leZP; rewrite Zpower_2_le leq_pred.
by rewrite s2Z_u2Z_pos' Z2uK.
Qed.

Lemma s2Z_Z2u' : forall {n:nat} (z:Z), -(2 ^^ Peano.pred n) <= z < 0 -> s2Z (Z2u n z) = z.
Proof.
(* PROVE ME! *)
Abort.

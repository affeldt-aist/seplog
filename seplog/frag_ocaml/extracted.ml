(*
 *  Seplog is an implementation of separation logic (an extension of Hoare
 *  logic by John C. Reynolds, Peter W. O'Hearn, and colleagues) in the
 *  Coq proof assistant (version 8, http://coq.inria.fr) together with a
 *  sample verification of the heap manager of the Topsy operating system
 *  (version 2, http://www.topsy.net). More information is available at
 *  http://staff.aist.go.jp/reynald.affeldt/seplog.
 *
 *  Copyright (c) 2005, 2006 Reynald Affeldt and Nicolas Marti
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *)
type bool =
  | True
  | False

type nat =
  | O
  | S of nat

type 'a option =
  | Some of 'a
  | None

type ('a, 'b) prod =
  | Pair of 'a * 'b

type comparison =
  | Eq
  | Lt
  | Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
  | Eq -> Eq
  | Lt -> Gt
  | Gt -> Lt

type sumbool =
  | Left
  | Right

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
    | O -> m
    | S p -> S (plus p m)

(** val mult : nat -> nat -> nat **)

let rec mult n m =
  match n with
    | O -> O
    | S p -> plus m (mult p m)

type 'a list =
  | Nil
  | Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
    | Nil -> m
    | Cons (a, l1) -> Cons (a, (app l1 m))

(** val length : 'a1 list -> nat **)

let rec length = function
  | Nil -> O
  | Cons (a, m) -> S (length m)

type positive =
  | XI of positive
  | XO of positive
  | XH

(** val psucc : positive -> positive **)

let rec psucc = function
  | XI x' -> XO (psucc x')
  | XO x' -> XI x'
  | XH -> XO XH

(** val pplus : positive -> positive -> positive **)

let rec pplus x y =
  match x with
    | XI x' ->
        (match y with
           | XI y' -> XO (pplus_carry x' y')
           | XO y' -> XI (pplus x' y')
           | XH -> XO (psucc x'))
    | XO x' ->
        (match y with
           | XI y' -> XI (pplus x' y')
           | XO y' -> XO (pplus x' y')
           | XH -> XI x')
    | XH ->
        (match y with
           | XI y' -> XO (psucc y')
           | XO y' -> XI y'
           | XH -> XO XH)

(** val pplus_carry : positive -> positive -> positive **)

and pplus_carry x y =
  match x with
    | XI x' ->
        (match y with
           | XI y' -> XI (pplus_carry x' y')
           | XO y' -> XO (pplus_carry x' y')
           | XH -> XI (psucc x'))
    | XO x' ->
        (match y with
           | XI y' -> XO (pplus_carry x' y')
           | XO y' -> XI (pplus x' y')
           | XH -> XO (psucc x'))
    | XH ->
        (match y with
           | XI y' -> XI (psucc y')
           | XO y' -> XO (psucc y')
           | XH -> XI XH)

(** val pmult_nat : positive -> nat -> nat **)

let rec pmult_nat x pow2 =
  match x with
    | XI x' -> plus pow2 (pmult_nat x' (plus pow2 pow2))
    | XO x' -> pmult_nat x' (plus pow2 pow2)
    | XH -> pow2

(** val nat_of_P : positive -> nat **)

let nat_of_P x =
  pmult_nat x (S O)

(** val p_of_succ_nat : nat -> positive **)

let rec p_of_succ_nat = function
  | O -> XH
  | S x' -> psucc (p_of_succ_nat x')

(** val pdouble_minus_one : positive -> positive **)

let rec pdouble_minus_one = function
  | XI x' -> XI (XO x')
  | XO x' -> XI (pdouble_minus_one x')
  | XH -> XH

type positive_mask =
  | IsNul
  | IsPos of positive
  | IsNeg

(** val pdouble_plus_one_mask : positive_mask -> positive_mask **)

let pdouble_plus_one_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

(** val pdouble_mask : positive_mask -> positive_mask **)

let pdouble_mask = function
  | IsNul -> IsNul
  | IsPos p -> IsPos (XO p)
  | IsNeg -> IsNeg

(** val pdouble_minus_two : positive -> positive_mask **)

let pdouble_minus_two = function
  | XI x' -> IsPos (XO (XO x'))
  | XO x' -> IsPos (XO (pdouble_minus_one x'))
  | XH -> IsNul

(** val pminus_mask : positive -> positive -> positive_mask **)

let rec pminus_mask x y =
  match x with
    | XI x' ->
        (match y with
           | XI y' -> pdouble_mask (pminus_mask x' y')
           | XO y' -> pdouble_plus_one_mask (pminus_mask x' y')
           | XH -> IsPos (XO x'))
    | XO x' ->
        (match y with
           | XI y' -> pdouble_plus_one_mask (pminus_mask_carry x' y')
           | XO y' -> pdouble_mask (pminus_mask x' y')
           | XH -> IsPos (pdouble_minus_one x'))
    | XH -> (match y with
               | XI p -> IsNeg
               | XO p -> IsNeg
               | XH -> IsNul)

(** val pminus_mask_carry : positive -> positive -> positive_mask **)

and pminus_mask_carry x y =
  match x with
    | XI x' ->
        (match y with
           | XI y' -> pdouble_plus_one_mask (pminus_mask_carry x' y')
           | XO y' -> pdouble_mask (pminus_mask x' y')
           | XH -> IsPos (pdouble_minus_one x'))
    | XO x' ->
        (match y with
           | XI y' -> pdouble_mask (pminus_mask_carry x' y')
           | XO y' -> pdouble_plus_one_mask (pminus_mask_carry x' y')
           | XH -> pdouble_minus_two x')
    | XH -> IsNeg

(** val pminus : positive -> positive -> positive **)

let pminus x y =
  match pminus_mask x y with
    | IsNul -> XH
    | IsPos z0 -> z0
    | IsNeg -> XH

(** val pmult : positive -> positive -> positive **)

let rec pmult x y =
  match x with
    | XI x' -> pplus y (XO (pmult x' y))
    | XO x' -> XO (pmult x' y)
    | XH -> y

(** val pcompare : positive -> positive -> comparison -> comparison **)

let rec pcompare x y r =
  match x with
    | XI x' ->
        (match y with
           | XI y' -> pcompare x' y' r
           | XO y' -> pcompare x' y' Gt
           | XH -> Gt)
    | XO x' ->
        (match y with
           | XI y' -> pcompare x' y' Lt
           | XO y' -> pcompare x' y' r
           | XH -> Gt)
    | XH -> (match y with
               | XI y' -> Lt
               | XO y' -> Lt
               | XH -> r)

type z =
  | Z0
  | Zpos of positive
  | Zneg of positive

(** val zplus : z -> z -> z **)

let zplus x y =
  match x with
    | Z0 -> y
    | Zpos x' ->
        (match y with
           | Z0 -> Zpos x'
           | Zpos y' -> Zpos (pplus x' y')
           | Zneg y' ->
               (match pcompare x' y' Eq with
                  | Eq -> Z0
                  | Lt -> Zneg (pminus y' x')
                  | Gt -> Zpos (pminus x' y')))
    | Zneg x' ->
        (match y with
           | Z0 -> Zneg x'
           | Zpos y' ->
               (match pcompare x' y' Eq with
                  | Eq -> Z0
                  | Lt -> Zpos (pminus y' x')
                  | Gt -> Zneg (pminus x' y'))
           | Zneg y' -> Zneg (pplus x' y'))

(** val zopp : z -> z **)

let zopp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

(** val zminus : z -> z -> z **)

let zminus m n =
  zplus m (zopp n)

(** val zmult : z -> z -> z **)

let zmult x y =
  match x with
    | Z0 -> Z0
    | Zpos x' ->
        (match y with
           | Z0 -> Z0
           | Zpos y' -> Zpos (pmult x' y')
           | Zneg y' -> Zneg (pmult x' y'))
    | Zneg x' ->
        (match y with
           | Z0 -> Z0
           | Zpos y' -> Zneg (pmult x' y')
           | Zneg y' -> Zpos (pmult x' y'))

(** val zcompare : z -> z -> comparison **)

let zcompare x y =
  match x with
    | Z0 -> (match y with
               | Z0 -> Eq
               | Zpos y' -> Lt
               | Zneg y' -> Gt)
    | Zpos x' ->
        (match y with
           | Z0 -> Gt
           | Zpos y' -> pcompare x' y' Eq
           | Zneg y' -> Gt)
    | Zneg x' ->
        (match y with
           | Z0 -> Lt
           | Zpos y' -> Lt
           | Zneg y' -> compOpp (pcompare x' y' Eq))

(** val z_of_nat : nat -> z **)

let z_of_nat = function
  | O -> Z0
  | S y -> Zpos (p_of_succ_nat y)

(** val eq_nat_dec : nat -> nat -> sumbool **)

let rec eq_nat_dec n m =
  match n with
    | O -> let rec f = function
             | O -> Left
             | S n1 -> Right
           in f m
    | S n0 -> (match m with
                 | O -> Right
                 | S n1 -> eq_nat_dec n0 n1)

(** val zge_bool : z -> z -> bool **)

let zge_bool x y =
  match zcompare x y with
    | Eq -> True
    | Lt -> False
    | Gt -> True

(** val zlt_bool : z -> z -> bool **)

let zlt_bool x y =
  match zcompare x y with
    | Eq -> False
    | Lt -> True
    | Gt -> False

(** val zeq_bool : z -> z -> bool **)

let zeq_bool x y =
  match zcompare x y with
    | Eq -> True
    | Lt -> False
    | Gt -> False

(** val negb : bool -> bool **)

let negb = function
  | True -> False
  | False -> True

(** val beq_nat : nat -> nat -> bool **)

let rec beq_nat n m =
  match n with
    | O -> (match m with
              | O -> True
              | S n0 -> False)
    | S n1 -> (match m with
                 | O -> False
                 | S m1 -> beq_nat n1 m1)

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
    | O -> m
    | S n' -> (match m with
                 | O -> n
                 | S m' -> S (max n' m'))

module Coq_valandloc = 
 struct 
  type loc = nat
  
  type coq_val = z
  
  (** val val2loc : z -> loc **)
  
  let val2loc = function
    | Z0 -> O
    | Zpos p -> nat_of_P p
    | Zneg p -> nat_of_P p
  
  (** val loc2val : loc -> coq_val **)
  
  let loc2val p =
    z_of_nat p
 end

module Coq_var = 
 struct 
  type v = nat
  
  (** val eqdec : nat -> nat -> sumbool **)
  
  let eqdec n m =
    eq_nat_dec n m
 end

type expr =
  | Var_e of Coq_var.v
  | Int_e of Coq_valandloc.coq_val
  | Add_e of expr * expr
  | Min_e of expr * expr
  | Mul_e of expr * expr
  | Div_e of expr * expr
  | Mod_e of expr * expr

(** val nat_e : nat -> expr **)

let nat_e x =
  Int_e (z_of_nat x)

(** val expr_var : expr -> Coq_var.v list **)

let rec expr_var = function
  | Var_e x -> Cons (x, Nil)
  | Int_e z0 -> Nil
  | Add_e (e1, e2) -> app (expr_var e1) (expr_var e2)
  | Min_e (e1, e2) -> app (expr_var e1) (expr_var e2)
  | Mul_e (e1, e2) -> app (expr_var e1) (expr_var e2)
  | Div_e (e1, e2) -> app (expr_var e1) (expr_var e2)
  | Mod_e (e1, e2) -> app (expr_var e1) (expr_var e2)

(** val expr_eq : expr -> expr -> bool **)

let rec expr_eq e1 e2 =
  match e1 with
    | Var_e w1 ->
        (match e2 with
           | Var_e w2 -> beq_nat w1 w2
           | Int_e v0 -> False
           | Add_e (e, e0) -> False
           | Min_e (e, e0) -> False
           | Mul_e (e, e0) -> False
           | Div_e (e, e0) -> False
           | Mod_e (e, e0) -> False)
    | Int_e i1 ->
        (match e2 with
           | Var_e v0 -> False
           | Int_e i2 -> zeq_bool i1 i2
           | Add_e (e, e0) -> False
           | Min_e (e, e0) -> False
           | Mul_e (e, e0) -> False
           | Div_e (e, e0) -> False
           | Mod_e (e, e0) -> False)
    | Add_e (e11, e12) ->
        (match e2 with
           | Var_e v0 -> False
           | Int_e v0 -> False
           | Add_e (e21, e22) ->
               (match expr_eq e11 e21 with
                  | True -> expr_eq e12 e22
                  | False -> False)
           | Min_e (e, e0) -> False
           | Mul_e (e, e0) -> False
           | Div_e (e, e0) -> False
           | Mod_e (e, e0) -> False)
    | Min_e (e11, e12) ->
        (match e2 with
           | Var_e v0 -> False
           | Int_e v0 -> False
           | Add_e (e, e0) -> False
           | Min_e (e21, e22) ->
               (match expr_eq e11 e21 with
                  | True -> expr_eq e12 e22
                  | False -> False)
           | Mul_e (e, e0) -> False
           | Div_e (e, e0) -> False
           | Mod_e (e, e0) -> False)
    | Mul_e (e11, e12) ->
        (match e2 with
           | Var_e v0 -> False
           | Int_e v0 -> False
           | Add_e (e, e0) -> False
           | Min_e (e, e0) -> False
           | Mul_e (e21, e22) ->
               (match expr_eq e11 e21 with
                  | True -> expr_eq e12 e22
                  | False -> False)
           | Div_e (e, e0) -> False
           | Mod_e (e, e0) -> False)
    | Div_e (e11, e12) ->
        (match e2 with
           | Var_e v0 -> False
           | Int_e v0 -> False
           | Add_e (e, e0) -> False
           | Min_e (e, e0) -> False
           | Mul_e (e, e0) -> False
           | Div_e (e21, e22) ->
               (match expr_eq e11 e21 with
                  | True -> expr_eq e12 e22
                  | False -> False)
           | Mod_e (e, e0) -> False)
    | Mod_e (e11, e12) ->
        (match e2 with
           | Var_e v0 -> False
           | Int_e v0 -> False
           | Add_e (e, e0) -> False
           | Min_e (e, e0) -> False
           | Mul_e (e, e0) -> False
           | Div_e (e, e0) -> False
           | Mod_e (e21, e22) ->
               (match expr_eq e11 e21 with
                  | True -> expr_eq e12 e22
                  | False -> False))

type expr_b =
  | True_b
  | Eq_b of expr * expr
  | Neq_b of expr * expr
  | Ge_b of expr * expr
  | Gt_b of expr * expr
  | Neg_b of expr_b
  | And_b of expr_b * expr_b
  | Or_b of expr_b * expr_b

(** val expr_b_var : expr_b -> Coq_var.v list **)

let rec expr_b_var = function
  | True_b -> Nil
  | Eq_b (e1, e2) -> app (expr_var e1) (expr_var e2)
  | Neq_b (e1, e2) -> app (expr_var e1) (expr_var e2)
  | Ge_b (e1, e2) -> app (expr_var e1) (expr_var e2)
  | Gt_b (e1, e2) -> app (expr_var e1) (expr_var e2)
  | Neg_b e0 -> expr_b_var e0
  | And_b (e1, e2) -> app (expr_b_var e1) (expr_b_var e2)
  | Or_b (e1, e2) -> app (expr_b_var e1) (expr_b_var e2)

type cmd =
  | Skip
  | Assign of Coq_var.v * expr
  | Lookup of Coq_var.v * expr
  | Mutation of expr * expr
  | Malloc of Coq_var.v * expr
  | Free of expr
  | While of expr_b * cmd
  | Seq of cmd * cmd
  | Ifte of expr_b * cmd * cmd

(** val inb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 -> bool **)

let rec inb b l a =
  match l with
    | Nil -> False
    | Cons (hd, tl) ->
        (match b a hd with
           | True -> True
           | False -> inb b tl a)

type constraint0 = expr

type andlist = constraint0 list

type orlist = andlist list

(** val dnf_expr_b1 : expr_b -> expr_b **)

let dnf_expr_b1 a = match a with
  | True_b -> a
  | Eq_b (e1, e2) -> And_b ((Ge_b (e2, e1)), (Ge_b (e1, e2)))
  | Neq_b (e, e0) -> a
  | Ge_b (e, e0) -> a
  | Gt_b (e1, e2) -> Ge_b (e1, (Add_e (e2, (nat_e (S O)))))
  | Neg_b e -> a
  | And_b (e, e0) -> a
  | Or_b (e, e0) -> a

(** val dnf_expr_b2 : expr_b -> expr_b **)

let dnf_expr_b2 a = match a with
  | True_b -> dnf_expr_b1 a
  | Eq_b (e, e0) -> dnf_expr_b1 a
  | Neq_b (e, e0) -> dnf_expr_b1 a
  | Ge_b (e, e0) -> dnf_expr_b1 a
  | Gt_b (e, e0) -> dnf_expr_b1 a
  | Neg_b e -> dnf_expr_b1 a
  | And_b (a1, a2) ->
      (match a1 with
         | True_b ->
             (match a2 with
                | True_b -> dnf_expr_b1 a
                | Eq_b (e, e0) -> dnf_expr_b1 a
                | Neq_b (e, e0) -> dnf_expr_b1 a
                | Ge_b (e, e0) -> dnf_expr_b1 a
                | Gt_b (e, e0) -> dnf_expr_b1 a
                | Neg_b e -> dnf_expr_b1 a
                | And_b (e, e0) -> dnf_expr_b1 a
                | Or_b (a3, a4) -> Or_b ((And_b (a1, a3)), (And_b (a1, a4))))
         | Eq_b (e, e0) ->
             (match a2 with
                | True_b -> dnf_expr_b1 a
                | Eq_b (e1, e2) -> dnf_expr_b1 a
                | Neq_b (e1, e2) -> dnf_expr_b1 a
                | Ge_b (e1, e2) -> dnf_expr_b1 a
                | Gt_b (e1, e2) -> dnf_expr_b1 a
                | Neg_b e1 -> dnf_expr_b1 a
                | And_b (e1, e2) -> dnf_expr_b1 a
                | Or_b (a3, a4) -> Or_b ((And_b (a1, a3)), (And_b (a1, a4))))
         | Neq_b (e, e0) ->
             (match a2 with
                | True_b -> dnf_expr_b1 a
                | Eq_b (e1, e2) -> dnf_expr_b1 a
                | Neq_b (e1, e2) -> dnf_expr_b1 a
                | Ge_b (e1, e2) -> dnf_expr_b1 a
                | Gt_b (e1, e2) -> dnf_expr_b1 a
                | Neg_b e1 -> dnf_expr_b1 a
                | And_b (e1, e2) -> dnf_expr_b1 a
                | Or_b (a3, a4) -> Or_b ((And_b (a1, a3)), (And_b (a1, a4))))
         | Ge_b (e, e0) ->
             (match a2 with
                | True_b -> dnf_expr_b1 a
                | Eq_b (e1, e2) -> dnf_expr_b1 a
                | Neq_b (e1, e2) -> dnf_expr_b1 a
                | Ge_b (e1, e2) -> dnf_expr_b1 a
                | Gt_b (e1, e2) -> dnf_expr_b1 a
                | Neg_b e1 -> dnf_expr_b1 a
                | And_b (e1, e2) -> dnf_expr_b1 a
                | Or_b (a3, a4) -> Or_b ((And_b (a1, a3)), (And_b (a1, a4))))
         | Gt_b (e, e0) ->
             (match a2 with
                | True_b -> dnf_expr_b1 a
                | Eq_b (e1, e2) -> dnf_expr_b1 a
                | Neq_b (e1, e2) -> dnf_expr_b1 a
                | Ge_b (e1, e2) -> dnf_expr_b1 a
                | Gt_b (e1, e2) -> dnf_expr_b1 a
                | Neg_b e1 -> dnf_expr_b1 a
                | And_b (e1, e2) -> dnf_expr_b1 a
                | Or_b (a3, a4) -> Or_b ((And_b (a1, a3)), (And_b (a1, a4))))
         | Neg_b e ->
             (match a2 with
                | True_b -> dnf_expr_b1 a
                | Eq_b (e0, e1) -> dnf_expr_b1 a
                | Neq_b (e0, e1) -> dnf_expr_b1 a
                | Ge_b (e0, e1) -> dnf_expr_b1 a
                | Gt_b (e0, e1) -> dnf_expr_b1 a
                | Neg_b e0 -> dnf_expr_b1 a
                | And_b (e0, e1) -> dnf_expr_b1 a
                | Or_b (a3, a4) -> Or_b ((And_b (a1, a3)), (And_b (a1, a4))))
         | And_b (e, e0) ->
             (match a2 with
                | True_b -> dnf_expr_b1 a
                | Eq_b (e1, e2) -> dnf_expr_b1 a
                | Neq_b (e1, e2) -> dnf_expr_b1 a
                | Ge_b (e1, e2) -> dnf_expr_b1 a
                | Gt_b (e1, e2) -> dnf_expr_b1 a
                | Neg_b e1 -> dnf_expr_b1 a
                | And_b (e1, e2) -> dnf_expr_b1 a
                | Or_b (a3, a4) -> Or_b ((And_b (a1, a3)), (And_b (a1, a4))))
         | Or_b (a3, a4) ->
             (match a2 with
                | True_b -> Or_b ((And_b (a2, a3)), (And_b (a2, a4)))
                | Eq_b (e, e0) -> Or_b ((And_b (a2, a3)), (And_b (a2, a4)))
                | Neq_b (e, e0) -> Or_b ((And_b (a2, a3)), (And_b (a2, a4)))
                | Ge_b (e, e0) -> Or_b ((And_b (a2, a3)), (And_b (a2, a4)))
                | Gt_b (e, e0) -> Or_b ((And_b (a2, a3)), (And_b (a2, a4)))
                | Neg_b e -> Or_b ((And_b (a2, a3)), (And_b (a2, a4)))
                | And_b (e, e0) -> Or_b ((And_b (a2, a3)), (And_b (a2, a4)))
                | Or_b (a5, a6) -> Or_b ((And_b (a1, a5)), (And_b (a1, a6)))))
  | Or_b (e, e0) -> dnf_expr_b1 a

(** val dnf_expr_b3 : expr_b -> expr_b **)

let dnf_expr_b3 a = match a with
  | True_b -> dnf_expr_b2 a
  | Eq_b (e, e0) -> dnf_expr_b2 a
  | Neq_b (e1, e2) -> Or_b ((Gt_b (e2, e1)), (Gt_b (e1, e2)))
  | Ge_b (e, e0) -> dnf_expr_b2 a
  | Gt_b (e, e0) -> dnf_expr_b2 a
  | Neg_b e ->
      (match e with
         | True_b -> dnf_expr_b2 a
         | Eq_b (e1, e2) -> Or_b ((Gt_b (e2, e1)), (Gt_b (e1, e2)))
         | Neq_b (e0, e1) -> dnf_expr_b2 a
         | Ge_b (e1, e2) -> Gt_b (e2, e1)
         | Gt_b (e1, e2) -> Ge_b (e2, e1)
         | Neg_b a' -> a'
         | And_b (a1, a2) -> Or_b ((Neg_b a1), (Neg_b a2))
         | Or_b (a1, a2) -> And_b ((Neg_b a1), (Neg_b a2)))
  | And_b (e, e0) -> dnf_expr_b2 a
  | Or_b (e, e0) -> dnf_expr_b2 a

(** val dnf_expr_rec : expr_b -> expr_b **)

let rec dnf_expr_rec a = match a with
  | True_b -> dnf_expr_b3 a
  | Eq_b (e, e0) -> dnf_expr_b3 a
  | Neq_b (e, e0) -> dnf_expr_b3 a
  | Ge_b (e, e0) -> dnf_expr_b3 a
  | Gt_b (e, e0) -> dnf_expr_b3 a
  | Neg_b e -> dnf_expr_b3 a
  | And_b (a1, a2) ->
      dnf_expr_b2 (And_b ((dnf_expr_rec a1), (dnf_expr_rec a2)))
  | Or_b (a1, a2) -> Or_b ((dnf_expr_rec a1), (dnf_expr_rec a2))

(** val expr_b_size : expr_b -> nat **)

let rec expr_b_size = function
  | True_b -> S O
  | Eq_b (e1, e2) -> S O
  | Neq_b (e1, e2) -> S O
  | Ge_b (e1, e2) -> S O
  | Gt_b (e1, e2) -> S O
  | Neg_b e -> plus (S O) (expr_b_size e)
  | And_b (e1, e2) -> plus (S O) (mult (expr_b_size e1) (expr_b_size e2))
  | Or_b (e1, e2) -> plus (S O) (plus (expr_b_size e1) (expr_b_size e2))

(** val dnf_expr_fp : expr_b -> nat -> expr_b **)

let rec dnf_expr_fp a = function
  | O -> dnf_expr_rec a
  | S n -> dnf_expr_fp (dnf_expr_rec a) n

(** val dnf_expr_b : expr_b -> expr_b **)

let dnf_expr_b a =
  dnf_expr_fp a (expr_b_size a)

(** val elim_expr_b_true : expr_b -> expr_b **)

let rec elim_expr_b_true a = match a with
  | True_b -> Eq_b ((Int_e Z0), (Int_e Z0))
  | Eq_b (e1, e2) -> a
  | Neq_b (e1, e2) -> a
  | Ge_b (e1, e2) -> a
  | Gt_b (e1, e2) -> a
  | Neg_b e -> Neg_b (elim_expr_b_true e)
  | And_b (e1, e2) -> And_b ((elim_expr_b_true e1), (elim_expr_b_true e2))
  | Or_b (e1, e2) -> Or_b ((elim_expr_b_true e1), (elim_expr_b_true e2))

(** val dnf_expr_b2constraint : expr_b -> constraint0 option **)

let dnf_expr_b2constraint = function
  | True_b -> None
  | Eq_b (e, e0) -> None
  | Neq_b (e, e0) -> None
  | Ge_b (e1, e2) -> Some (Min_e (e2, e1))
  | Gt_b (e, e0) -> None
  | Neg_b e -> None
  | And_b (e, e0) -> None
  | Or_b (e, e0) -> None

(** val dnf_expr_b2andlist : expr_b -> andlist option **)

let rec dnf_expr_b2andlist b = match b with
  | True_b ->
      (match dnf_expr_b2constraint b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Eq_b (e, e0) ->
      (match dnf_expr_b2constraint b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Neq_b (e, e0) ->
      (match dnf_expr_b2constraint b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Ge_b (e, e0) ->
      (match dnf_expr_b2constraint b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Gt_b (e, e0) ->
      (match dnf_expr_b2constraint b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Neg_b e ->
      (match dnf_expr_b2constraint b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | And_b (b1, b2) ->
      (match dnf_expr_b2andlist b1 with
         | Some l1' ->
             (match dnf_expr_b2andlist b2 with
                | Some l2' -> Some (app l1' l2')
                | None -> None)
         | None -> None)
  | Or_b (e, e0) ->
      (match dnf_expr_b2constraint b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)

(** val dnf_expr_b2orlist : expr_b -> orlist option **)

let rec dnf_expr_b2orlist b = match b with
  | True_b ->
      (match dnf_expr_b2andlist b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Eq_b (e, e0) ->
      (match dnf_expr_b2andlist b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Neq_b (e, e0) ->
      (match dnf_expr_b2andlist b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Ge_b (e, e0) ->
      (match dnf_expr_b2andlist b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Gt_b (e, e0) ->
      (match dnf_expr_b2andlist b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Neg_b e ->
      (match dnf_expr_b2andlist b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | And_b (e, e0) ->
      (match dnf_expr_b2andlist b with
         | Some b' -> Some (Cons (b', Nil))
         | None -> None)
  | Or_b (b1, b2) ->
      (match dnf_expr_b2orlist b1 with
         | Some l1' ->
             (match dnf_expr_b2orlist b2 with
                | Some l2' -> Some (app l1' l2')
                | None -> None)
         | None -> None)

(** val expr_b2constraints : expr_b -> orlist option **)

let expr_b2constraints b =
  dnf_expr_b2orlist (dnf_expr_b (elim_expr_b_true b))

(** val expr_compute : expr -> z option **)

let rec expr_compute = function
  | Var_e x -> None
  | Int_e x -> Some x
  | Add_e (e1, e2) ->
      (match expr_compute e1 with
         | Some e1' ->
             (match expr_compute e2 with
                | Some e2' -> Some (zplus e1' e2')
                | None -> None)
         | None -> None)
  | Min_e (e1, e2) ->
      (match expr_compute e1 with
         | Some e1' ->
             (match expr_compute e2 with
                | Some e2' -> Some (zminus e1' e2')
                | None -> None)
         | None -> None)
  | Mul_e (e1, e2) ->
      (match expr_compute e1 with
         | Some e1' ->
             (match zeq_bool e1' Z0 with
                | True -> Some Z0
                | False ->
                    (match expr_compute e2 with
                       | Some e2' -> Some (zmult e1' e2')
                       | None -> None))
         | None ->
             (match expr_compute e2 with
                | Some e2' ->
                    (match zeq_bool e2' Z0 with
                       | True -> Some Z0
                       | False -> None)
                | None -> None))
  | Div_e (e0, e1) -> None
  | Mod_e (e0, e1) -> None

(** val expr_var_fact' : expr -> nat -> (expr, expr) prod **)

let rec expr_var_fact' e v0 =
  match e with
    | Var_e x ->
        (match beq_nat x v0 with
           | True -> Pair ((nat_e (S O)), (nat_e O))
           | False -> Pair ((nat_e O), (Var_e x)))
    | Int_e x -> Pair ((nat_e O), (Int_e x))
    | Add_e (e1, e2) ->
        let Pair (e11, e12) = expr_var_fact' e1 v0 in
        let Pair (e21, e22) = expr_var_fact' e2 v0 in
        Pair ((Add_e (e11, e21)), (Add_e (e12, e22)))
    | Min_e (e1, e2) ->
        let Pair (e11, e12) = expr_var_fact' e1 v0 in
        let Pair (e21, e22) = expr_var_fact' e2 v0 in
        Pair ((Min_e (e11, e21)), (Min_e (e12, e22)))
    | Mul_e (e1, e2) ->
        let Pair (e11, e12) = expr_var_fact' e1 v0 in
        let Pair (e21, e22) = expr_var_fact' e2 v0 in
        Pair ((Add_e ((Add_e ((Mul_e (e12, e21)), (Mul_e (e11, e22)))),
        (Mul_e ((Var_e v0), (Mul_e (e11, e21)))))), (Mul_e (e12, e22)))
    | Div_e (e1, e2) -> Pair ((nat_e O), (Div_e (e1, e2)))
    | Mod_e (e1, e2) -> Pair ((nat_e O), (Mod_e (e1, e2)))

(** val simpl_varlist_constraint : constraint0 -> nat list -> constraint0 **)

let rec simpl_varlist_constraint c = function
  | Nil ->
      (match expr_compute c with
         | Some val0 -> Int_e val0
         | None -> c)
  | Cons (hd, tl) ->
      let Pair (e1, e2) = expr_var_fact' c hd in
      (match expr_compute e1 with
         | Some val0 ->
             (match zeq_bool val0 Z0 with
                | True -> simpl_varlist_constraint e2 tl
                | False -> Add_e ((Mul_e ((Int_e val0), (Var_e hd))),
                    (simpl_varlist_constraint e2 tl)))
         | None -> Add_e ((Mul_e (e1, (Var_e hd))),
             (simpl_varlist_constraint e2 tl)))

(** val simpl_constraint : constraint0 -> constraint0 **)

let simpl_constraint c =
  simpl_varlist_constraint c (expr_var c)

(** val simpl_constraint_var' : constraint0 -> nat -> constraint0 **)

let simpl_constraint_var' c v0 =
  let Pair (e1, e2) = expr_var_fact' c v0 in
  (match expr_compute (simpl_constraint e1) with
     | Some val0 ->
         (match zeq_bool val0 Z0 with
            | True -> e2
            | False -> Add_e ((Mul_e ((Int_e val0), (Var_e v0))), e2))
     | None -> Add_e ((Mul_e (e1, (Var_e v0))), e2))

(** val simpl_constraint_var_list' : constraint0 -> nat list -> constraint0 **)

let rec simpl_constraint_var_list' c = function
  | Nil -> simpl_constraint c
  | Cons (hd, tl) ->
      simpl_constraint_var_list' (simpl_constraint_var' c hd) tl

(** val simpl_constraint' : constraint0 -> constraint0 **)

let simpl_constraint' c =
  simpl_constraint_var_list' c (expr_var c)

(** val expr_var_fact : expr -> nat -> (expr, expr) prod **)

let expr_var_fact e v0 =
  let Pair (e1, e2) = expr_var_fact' e v0 in
  Pair ((simpl_constraint e1), (simpl_constraint e2))

(** val simpl_andlist : andlist -> andlist **)

let rec simpl_andlist = function
  | Nil -> Nil
  | Cons (hd, tl) -> Cons ((simpl_constraint' hd), (simpl_andlist tl))

(** val simpl_orlist : orlist -> orlist **)

let rec simpl_orlist = function
  | Nil -> Nil
  | Cons (hd, tl) -> Cons ((simpl_andlist hd), (simpl_orlist tl))

(** val elim_var_constraint : constraint0 -> constraint0 -> nat ->
                              constraint0 **)

let elim_var_constraint c1 c2 v0 =
  let Pair (e11, e12) = expr_var_fact c1 v0 in
  let Pair (e21, e22) = expr_var_fact c2 v0 in
  (match expr_compute (simpl_constraint e11) with
     | Some e11' ->
         (match expr_compute (simpl_constraint e21) with
            | Some e21' ->
                (match match zlt_bool e11' Z0 with
                         | True -> zlt_bool Z0 e21'
                         | False -> False with
                   | True -> Min_e ((Mul_e (e21, e12)), (Mul_e (e11, e22)))
                   | False ->
                       (match match zlt_bool Z0 e11' with
                                | True -> zlt_bool e21' Z0
                                | False -> False with
                          | True -> Min_e ((Mul_e (e11, e22)), (Mul_e (e21,
                              e12)))
                          | False -> c2))
            | None -> c2)
     | None -> c2)

(** val elim_var_andlist' : constraint0 -> andlist -> andlist -> nat ->
                            andlist **)

let rec elim_var_andlist' c l l' v0 =
  match l with
    | Nil -> l'
    | Cons (hd, tl) ->
        (match inb beq_nat
                 (expr_var (simpl_constraint_var_list' hd (Cons (v0, Nil))))
                 v0 with
           | True ->
               elim_var_andlist' c tl (Cons ((elim_var_constraint c hd v0),
                 l')) v0
           | False -> elim_var_andlist' c tl l' v0)

(** val elim_var_andlist : andlist -> andlist -> nat -> andlist **)

let rec elim_var_andlist l l' v0 =
  match l with
    | Nil -> l'
    | Cons (hd, tl) ->
        (match inb beq_nat
                 (expr_var (simpl_constraint_var_list' hd (Cons (v0, Nil))))
                 v0 with
           | True ->
               elim_var_andlist tl (app l' (elim_var_andlist' hd tl Nil v0))
                 v0
           | False -> elim_var_andlist tl (Cons (hd, l')) v0)

(** val elim_var_orlist : orlist -> nat -> orlist **)

let rec elim_var_orlist l v0 =
  match l with
    | Nil -> Nil
    | Cons (hd, tl) -> Cons ((elim_var_andlist hd Nil v0),
        (elim_var_orlist tl v0))

(** val elim_varlist_orlist : orlist -> nat list -> orlist **)

let rec elim_varlist_orlist l = function
  | Nil -> l
  | Cons (hd, tl) -> elim_varlist_orlist (elim_var_orlist l hd) tl

(** val eval_constraint : constraint0 -> bool option **)

let eval_constraint c =
  match expr_compute c with
    | Some z0 -> Some (zge_bool Z0 z0)
    | None -> None

(** val eval_andlist' : andlist -> bool option **)

let rec eval_andlist' = function
  | Nil -> Some True
  | Cons (hd, tl) ->
      (match eval_constraint hd with
         | Some b ->
             (match b with
                | True ->
                    (match eval_andlist' tl with
                       | Some b0 ->
                           (match b0 with
                              | True ->
                                  (match eval_constraint hd with
                                     | Some a' -> Some a'
                                     | None -> None)
                              | False -> Some False)
                       | None -> None)
                | False -> Some False)
         | None ->
             (match eval_andlist' tl with
                | Some b ->
                    (match b with
                       | True ->
                           (match eval_constraint hd with
                              | Some a' -> Some a'
                              | None -> None)
                       | False -> Some False)
                | None -> None))

(** val eval_andlist : andlist -> bool option **)

let eval_andlist a =
  match beq_nat (length a) O with
    | True -> None
    | False -> eval_andlist' a

(** val eval_orlist' : orlist -> bool option **)

let rec eval_orlist' = function
  | Nil -> Some False
  | Cons (hd, tl) ->
      (match eval_andlist hd with
         | Some a' ->
             (match eval_orlist' tl with
                | Some b' -> Some
                    (match a' with
                       | True -> True
                       | False -> b')
                | None -> None)
         | None -> None)

(** val eval_orlist : orlist -> bool option **)

let eval_orlist a =
  match beq_nat (length a) O with
    | True -> None
    | False -> eval_orlist' a

(** val presburgerB : expr_b -> bool **)

let presburgerB b =
  match expr_b2constraints (Neg_b b) with
    | Some ol ->
        (match eval_orlist
                 (simpl_orlist (elim_varlist_orlist ol (expr_b_var b))) with
           | Some res -> negb res
           | None -> False)
    | None -> False

type pi = expr_b

type sigma =
  | Singl of expr * expr
  | Cell of expr
  | Epsi
  | Star of sigma * sigma

type assrt = (pi, sigma) prod

(** val sigma_clean_epsi : sigma -> sigma **)

let rec sigma_clean_epsi t = match t with
  | Singl (e, e0) -> t
  | Cell e -> t
  | Epsi -> t
  | Star (t1, t2) ->
      (match sigma_clean_epsi t1 with
         | Singl (e, e0) ->
             (match sigma_clean_epsi t2 with
                | Singl (e1, e2) -> Star ((sigma_clean_epsi t1),
                    (sigma_clean_epsi t2))
                | Cell e1 -> Star ((sigma_clean_epsi t1),
                    (sigma_clean_epsi t2))
                | Epsi -> sigma_clean_epsi t1
                | Star (s, s0) -> Star ((sigma_clean_epsi t1),
                    (sigma_clean_epsi t2)))
         | Cell e ->
             (match sigma_clean_epsi t2 with
                | Singl (e0, e1) -> Star ((sigma_clean_epsi t1),
                    (sigma_clean_epsi t2))
                | Cell e0 -> Star ((sigma_clean_epsi t1),
                    (sigma_clean_epsi t2))
                | Epsi -> sigma_clean_epsi t1
                | Star (s, s0) -> Star ((sigma_clean_epsi t1),
                    (sigma_clean_epsi t2)))
         | Epsi -> sigma_clean_epsi t2
         | Star (s, s0) ->
             (match sigma_clean_epsi t2 with
                | Singl (e, e0) -> Star ((sigma_clean_epsi t1),
                    (sigma_clean_epsi t2))
                | Cell e -> Star ((sigma_clean_epsi t1),
                    (sigma_clean_epsi t2))
                | Epsi -> sigma_clean_epsi t1
                | Star (s1, s2) -> Star ((sigma_clean_epsi t1),
                    (sigma_clean_epsi t2))))

(** val sigma_elt_eq : sigma -> sigma -> pi -> bool **)

let sigma_elt_eq e1 e2 env =
  match e1 with
    | Singl (x1, x2) ->
        (match e2 with
           | Singl (x3, x4) ->
               (match presburgerB (Or_b ((Neg_b env), (Eq_b (x1, x3)))) with
                  | True -> presburgerB (Or_b ((Neg_b env), (Eq_b (x2, x4))))
                  | False -> False)
           | Cell x3 -> presburgerB (Or_b ((Neg_b env), (Eq_b (x1, x3))))
           | Epsi -> False
           | Star (s, s0) -> False)
    | Cell x1 ->
        (match e2 with
           | Singl (e, e0) -> False
           | Cell x3 -> presburgerB (Or_b ((Neg_b env), (Eq_b (x1, x3))))
           | Epsi -> False
           | Star (s, s0) -> False)
    | Epsi ->
        (match e2 with
           | Singl (e, e0) -> False
           | Cell e -> False
           | Epsi -> True
           | Star (s, s0) -> False)
    | Star (s, s0) -> False

(** val sigma_elt_term_extract : sigma -> sigma -> pi -> sigma option **)

let rec sigma_elt_term_extract e t env =
  match t with
    | Singl (e0, e1) ->
        (match sigma_elt_eq e t env with
           | True -> Some Epsi
           | False -> None)
    | Cell e0 ->
        (match sigma_elt_eq e t env with
           | True -> Some Epsi
           | False -> None)
    | Epsi ->
        (match sigma_elt_eq e t env with
           | True -> Some Epsi
           | False -> None)
    | Star (t1, t2) ->
        (match sigma_elt_term_extract e t1 env with
           | Some t1' -> Some (sigma_clean_epsi (Star (t1', t2)))
           | None ->
               (match sigma_elt_term_extract e t2 env with
                  | Some t2' -> Some (sigma_clean_epsi (Star (t1, t2')))
                  | None -> None))

(** val sigma_elt_term_extract' : sigma -> sigma -> pi -> sigma option **)

let rec sigma_elt_term_extract' e t env =
  match t with
    | Singl (e0, e1) ->
        (match sigma_elt_eq t e env with
           | True -> Some Epsi
           | False -> None)
    | Cell e0 ->
        (match sigma_elt_eq t e env with
           | True -> Some Epsi
           | False -> None)
    | Epsi ->
        (match sigma_elt_eq t e env with
           | True -> Some Epsi
           | False -> None)
    | Star (t1, t2) ->
        (match sigma_elt_term_extract' e t1 env with
           | Some t1' -> Some (sigma_clean_epsi (Star (t1', t2)))
           | None ->
               (match sigma_elt_term_extract' e t2 env with
                  | Some t2' -> Some (sigma_clean_epsi (Star (t1, t2')))
                  | None -> None))

(** val sigma_term_term_eq : sigma -> sigma -> pi -> sigma option **)

let rec sigma_term_term_eq t1 t2 env =
  match t1 with
    | Singl (e, e0) ->
        (match sigma_elt_term_extract t1 t2 env with
           | Some t2' -> Some t2'
           | None -> None)
    | Cell e ->
        (match sigma_elt_term_extract t1 t2 env with
           | Some t2' -> Some t2'
           | None -> None)
    | Epsi ->
        (match sigma_elt_term_extract t1 t2 env with
           | Some t2' -> Some t2'
           | None -> None)
    | Star (t11, t12) ->
        (match sigma_term_term_eq t11 t2 env with
           | Some t2' ->
               (match sigma_term_term_eq t12 t2' env with
                  | Some t2'' -> Some t2''
                  | None -> None)
           | None -> None)

(** val sigma_get_cell_val : expr -> sigma -> pi -> expr option **)

let rec sigma_get_cell_val e sig0 env =
  match sig0 with
    | Singl (e1, e2) ->
        (match presburgerB (Or_b ((Neg_b env), (Eq_b (e1, e)))) with
           | True -> Some e2
           | False -> None)
    | Cell e1 -> None
    | Epsi -> None
    | Star (s1, s2) ->
        (match sigma_get_cell_val e s1 env with
           | Some e2 -> Some e2
           | None -> sigma_get_cell_val e s2 env)

(** val frag_decision : (pi, sigma) prod -> (pi, sigma) prod -> bool **)

let frag_decision p q =
  let Pair (pi1, sig1) = p in
  let Pair (pi2, sig2) = q in
  (match presburgerB (Or_b ((Neg_b pi1), pi2)) with
     | True ->
         (match sigma_term_term_eq sig1 sig2 pi1 with
            | Some s ->
                (match s with
                   | Singl (e, e0) -> False
                   | Cell e -> False
                   | Epsi -> True
                   | Star (s0, s1) -> False)
            | None -> False)
     | False -> False)

type l_assrt =
  | L_elt of assrt
  | L_subst of (Coq_var.v, expr) prod list * l_assrt
  | L_lookup of Coq_var.v * expr * l_assrt
  | L_mutation of expr * expr * l_assrt
  | L_if of expr_b * l_assrt * l_assrt

(** val subst_e : expr -> expr -> expr -> expr **)

let rec subst_e e patt repl =
  match e with
    | Var_e w -> (match expr_eq e patt with
                    | True -> repl
                    | False -> e)
    | Int_e i -> (match expr_eq e patt with
                    | True -> repl
                    | False -> e)
    | Add_e (e1, e2) ->
        (match expr_eq e patt with
           | True -> repl
           | False -> Add_e ((subst_e e1 patt repl), (subst_e e2 patt repl)))
    | Min_e (e1, e2) ->
        (match expr_eq e patt with
           | True -> repl
           | False -> Min_e ((subst_e e1 patt repl), (subst_e e2 patt repl)))
    | Mul_e (e1, e2) ->
        (match expr_eq e patt with
           | True -> repl
           | False -> Mul_e ((subst_e e1 patt repl), (subst_e e2 patt repl)))
    | Div_e (e1, e2) ->
        (match expr_eq e patt with
           | True -> repl
           | False -> Div_e ((subst_e e1 patt repl), (subst_e e2 patt repl)))
    | Mod_e (e1, e2) ->
        (match expr_eq e patt with
           | True -> repl
           | False -> Mod_e ((subst_e e1 patt repl), (subst_e e2 patt repl)))

(** val subst_b : expr_b -> expr -> expr -> expr_b **)

let rec subst_b e patt repl =
  match e with
    | True_b -> True_b
    | Eq_b (f, g) -> Eq_b ((subst_e f patt repl), (subst_e g patt repl))
    | Neq_b (f, g) -> Neq_b ((subst_e f patt repl), (subst_e g patt repl))
    | Ge_b (f, g) -> Ge_b ((subst_e f patt repl), (subst_e g patt repl))
    | Gt_b (f, g) -> Gt_b ((subst_e f patt repl), (subst_e g patt repl))
    | Neg_b e0 -> Neg_b (subst_b e0 patt repl)
    | And_b (f, g) -> And_b ((subst_b f patt repl), (subst_b g patt repl))
    | Or_b (f, g) -> Or_b ((subst_b f patt repl), (subst_b g patt repl))

(** val subst_Sigma : sigma -> Coq_var.v -> expr -> sigma **)

let rec subst_Sigma a x e =
  match a with
    | Singl (e1, e2) -> Singl ((subst_e e1 (Var_e x) e),
        (subst_e e2 (Var_e x) e))
    | Cell e1 -> Cell (subst_e e1 (Var_e x) e)
    | Epsi -> Epsi
    | Star (s1, s2) -> Star ((subst_Sigma s1 x e), (subst_Sigma s2 x e))

(** val subst_assrt : assrt -> Coq_var.v -> expr -> assrt **)

let subst_assrt a x e =
  let Pair (pi0, sigm) = a in
  Pair ((subst_b pi0 (Var_e x) e), (subst_Sigma sigm x e))

(** val subst_assrt_lst : (Coq_var.v, expr) prod list -> assrt -> assrt **)

let rec subst_assrt_lst l a =
  match l with
    | Nil -> a
    | Cons (p, tl) ->
        let Pair (x, e) = p in subst_assrt_lst tl (subst_assrt a x e)

(** val subst_e_lst : (Coq_var.v, expr) prod list -> expr -> expr **)

let rec subst_e_lst l e =
  match l with
    | Nil -> e
    | Cons (p, tl) ->
        let Pair (x, e') = p in subst_e_lst tl (subst_e e (Var_e x) e')

(** val subst_b_lst : (Coq_var.v, expr) prod list -> expr_b -> expr_b **)

let rec subst_b_lst l e =
  match l with
    | Nil -> e
    | Cons (p, tl) ->
        let Pair (x, e') = p in subst_b_lst tl (subst_b e (Var_e x) e')

module Fresh = 
 struct 
  (** val var_max_expr : expr -> Coq_var.v **)
  
  let rec var_max_expr = function
    | Var_e w -> w
    | Int_e i -> O
    | Add_e (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
    | Min_e (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
    | Mul_e (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
    | Div_e (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
    | Mod_e (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
  
  (** val var_max_expr_b : expr_b -> Coq_var.v **)
  
  let rec var_max_expr_b = function
    | True_b -> O
    | Eq_b (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
    | Neq_b (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
    | Ge_b (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
    | Gt_b (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
    | Neg_b e0 -> var_max_expr_b e0
    | And_b (e1, e2) -> max (var_max_expr_b e1) (var_max_expr_b e2)
    | Or_b (e1, e2) -> max (var_max_expr_b e1) (var_max_expr_b e2)
  
  (** val var_max_Sigma : sigma -> Coq_var.v **)
  
  let rec var_max_Sigma = function
    | Singl (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
    | Cell e1 -> var_max_expr e1
    | Epsi -> O
    | Star (s1, s2) -> max (var_max_Sigma s1) (var_max_Sigma s2)
  
  (** val var_max_assrt : assrt -> Coq_var.v **)
  
  let var_max_assrt = function
    | Pair (pi0, sigm) -> max (var_max_expr_b pi0) (var_max_Sigma sigm)
  
  (** val var_max_lst : (Coq_var.v, expr) prod list -> Coq_var.v **)
  
  let rec var_max_lst = function
    | Nil -> O
    | Cons (p, tl) ->
        let Pair (v0, e) = p in
        max (max v0 (var_max_expr e)) (var_max_lst tl)
  
  (** val var_max_L_assrt : l_assrt -> Coq_var.v **)
  
  let rec var_max_L_assrt = function
    | L_elt a1 -> var_max_assrt a1
    | L_subst (l, l0) -> max (var_max_lst l) (var_max_L_assrt l0)
    | L_lookup (x, e, l) -> max (max x (var_max_expr e)) (var_max_L_assrt l)
    | L_mutation (e1, e2, l) ->
        max (max (var_max_expr e1) (var_max_expr e2)) (var_max_L_assrt l)
    | L_if (b, l1, l2) ->
        max (max (var_max_L_assrt l1) (var_max_L_assrt l2))
          (var_max_expr_b b)
 end

(** val wp_frag : l_assrt option -> cmd -> l_assrt option **)

let rec wp_frag q = function
  | Skip -> (match q with
               | Some q' -> Some q'
               | None -> None)
  | Assign (v0, e) ->
      (match q with
         | Some q' -> Some (L_subst ((Cons ((Pair (v0, e)), Nil)), q'))
         | None -> None)
  | Lookup (v0, e) ->
      (match q with
         | Some q' -> Some (L_lookup (v0, e, q'))
         | None -> None)
  | Mutation (e1, e2) ->
      (match q with
         | Some q' -> Some (L_mutation (e1, e2, q'))
         | None -> None)
  | Malloc (v0, e) -> None
  | Free e -> None
  | While (a, c0) -> None
  | Seq (c1, c2) -> wp_frag (wp_frag q c2) c1
  | Ifte (b, c1, c2) ->
      (match wp_frag q c1 with
         | Some q1 ->
             (match wp_frag q c2 with
                | Some q2 -> Some (L_if (b, q1, q2))
                | None -> None)
         | None -> None)

(** val lWP_step : pi -> sigma -> l_assrt -> ((pi, sigma) prod, l_assrt) prod
                   list option **)

let lWP_step pi0 sig0 = function
  | L_elt l ->
      (match frag_decision (Pair (pi0, sig0)) l with
         | True -> Some Nil
         | False -> None)
  | L_subst (l, l0) ->
      (match l0 with
         | L_elt l' -> Some (Cons ((Pair ((Pair (pi0, sig0)), (L_elt
             (subst_assrt_lst l l')))), Nil))
         | L_subst (l', l'0) -> Some (Cons ((Pair ((Pair (pi0, sig0)),
             (L_subst ((app l' l), l'0)))), Nil))
         | L_lookup (x, e, l') ->
             (match sigma_get_cell_val (subst_e_lst l e) sig0 pi0 with
                | Some e' ->
                    let x' =
                      plus
                        (max
                          (max (Fresh.var_max_lst l)
                            (Fresh.var_max_L_assrt l')) x) (S O)
                    in
                    Some (Cons ((Pair ((Pair (pi0, sig0)), (L_subst ((Cons
                    ((Pair (x, (Var_e x'))),
                    (app l (Cons ((Pair (x', e')), Nil))))), l')))), Nil))
                | None -> None)
         | L_mutation (e1, e2, l') -> Some (Cons ((Pair ((Pair (pi0, sig0)),
             (L_mutation ((subst_e_lst l e1), (subst_e_lst l e2), (L_subst
             (l, l')))))), Nil))
         | L_if (b, l1, l2) -> Some (Cons ((Pair ((Pair (pi0, sig0)), (L_if
             ((subst_b_lst l b), (L_subst (l, l1)), (L_subst (l, l2)))))),
             Nil)))
  | L_lookup (x, e, l) ->
      (match sigma_get_cell_val e sig0 pi0 with
         | Some e' -> Some (Cons ((Pair ((Pair (pi0, sig0)), (L_subst ((Cons
             ((Pair (x, e')), Nil)), l)))), Nil))
         | None -> None)
  | L_mutation (e1, e2, l) ->
      (match sigma_elt_term_extract' (Cell e1) sig0 pi0 with
         | Some sig' -> Some (Cons ((Pair ((Pair (pi0, (Star ((Singl (e1,
             e2)), sig')))), l)), Nil))
         | None -> None)
  | L_if (b, l1, l2) -> Some (Cons ((Pair ((Pair ((And_b (pi0, b)), sig0)),
      l1)), (Cons ((Pair ((Pair ((And_b (pi0, (Neg_b b))), sig0)), l2)),
      Nil))))

(** val l_assrt_size : l_assrt -> nat **)

let rec l_assrt_size = function
  | L_elt p -> S (S O)
  | L_subst (l, p) -> plus (S (S O)) (l_assrt_size p)
  | L_lookup (x, e, p) -> plus (S (S O)) (l_assrt_size p)
  | L_mutation (e1, e2, p) -> plus (S (S O)) (l_assrt_size p)
  | L_if (b, l1, l2) ->
      plus (plus (S (S O)) (l_assrt_size l1)) (l_assrt_size l2)

(** val lWP_list : ((pi, sigma) prod, l_assrt) prod list -> ((pi, sigma)
                   prod, l_assrt) prod list option **)

let rec lWP_list = function
  | Nil -> Some Nil
  | Cons (p, tl) ->
      let Pair (p0, a) = p in
      let Pair (pi0, sig0) = p0 in
      (match lWP_step pi0 sig0 a with
         | Some l' ->
             (match lWP_list tl with
                | Some l'' -> Some (app l' l'')
                | None -> None)
         | None -> None)

(** val lWP_list_rec : ((pi, sigma) prod, l_assrt) prod list -> nat -> ((pi,
                       sigma) prod, l_assrt) prod list option **)

let rec lWP_list_rec l = function
  | O -> Some l
  | S size' ->
      (match lWP_list l with
         | Some l' -> lWP_list_rec l' size'
         | None -> None)

(** val frag_hoare : (pi, sigma) prod -> (pi, sigma) prod -> cmd -> bool **)

let frag_hoare p q c =
  match wp_frag (Some (L_elt q)) c with
    | Some l ->
        let Pair (p0, s) = p in
        (match lWP_list_rec (Cons ((Pair ((Pair (p0, s)), l)), Nil))
                 (l_assrt_size l) with
           | Some l0 ->
               (match l0 with
                  | Nil -> True
                  | Cons (p1, l1) -> False)
           | None -> False)
    | None -> False


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

(** val negb : bool -> bool **)

let negb = function
  | True -> False
  | False -> True

type 'a list =
  | Nil
  | Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
  | Nil -> O
  | Cons (a, m) -> S (length m)

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
    | Nil -> m
    | Cons (a, l1) -> Cons (a, (app l1 m))

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
    | O -> (match m with
              | O -> Left
              | S m0 -> Right)
    | S n0 -> (match m with
                 | O -> Right
                 | S m0 -> eq_nat_dec n0 m0)

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

type val0 = z

module Coq_var = 
 struct 
  type v = nat
  
  (** val eqdec : nat -> nat -> sumbool **)
  
  let eqdec n m =
    eq_nat_dec n m
 end

type expr =
  | Var_e of Coq_var.v
  | Int_e of val0
  | Add_e of expr * expr
  | Min_e of expr * expr
  | Mul_e of expr * expr
  | Div_e of expr * expr
  | Mod_e of expr * expr

(** val nat_e : nat -> expr **)

let nat_e x =
  Int_e (z_of_nat x)

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

(** val add_elt_list : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 -> 'a1 list **)

let rec add_elt_list b l a =
  match l with
    | Nil -> Cons (a, Nil)
    | Cons (hd, tl) ->
        (match b hd a with
           | True -> l
           | False -> Cons (hd, (add_elt_list b tl a)))

(** val app_list : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec app_list b l1 l2 =
  match l1 with
    | Nil -> l2
    | Cons (hd, tl) -> app_list b tl (add_elt_list b l2 hd)

(** val expr_var : expr -> Coq_var.v list **)

let rec expr_var = function
  | Var_e x -> Cons (x, Nil)
  | Int_e z0 -> Nil
  | Add_e (e1, e2) -> app_list beq_nat (expr_var e1) (expr_var e2)
  | Min_e (e1, e2) -> app_list beq_nat (expr_var e1) (expr_var e2)
  | Mul_e (e1, e2) -> app_list beq_nat (expr_var e1) (expr_var e2)
  | Div_e (e1, e2) -> app_list beq_nat (expr_var e1) (expr_var e2)
  | Mod_e (e1, e2) -> app_list beq_nat (expr_var e1) (expr_var e2)

(** val expr_B_var : expr_b -> Coq_var.v list **)

let rec expr_B_var = function
  | True_b -> Nil
  | Eq_b (e1, e2) -> app_list beq_nat (expr_var e1) (expr_var e2)
  | Neq_b (e1, e2) -> app_list beq_nat (expr_var e1) (expr_var e2)
  | Ge_b (e1, e2) -> app_list beq_nat (expr_var e1) (expr_var e2)
  | Gt_b (e1, e2) -> app_list beq_nat (expr_var e1) (expr_var e2)
  | Neg_b e0 -> expr_B_var e0
  | And_b (e1, e2) -> app_list beq_nat (expr_B_var e1) (expr_B_var e2)
  | Or_b (e1, e2) -> app_list beq_nat (expr_B_var e1) (expr_B_var e2)

(** val expr_B_size : expr_b -> nat **)

let rec expr_B_size = function
  | True_b -> S O
  | Eq_b (e1, e2) -> S O
  | Neq_b (e1, e2) -> S O
  | Ge_b (e1, e2) -> S O
  | Gt_b (e1, e2) -> S O
  | Neg_b e0 -> plus (S O) (expr_B_size e0)
  | And_b (e1, e2) -> plus (plus (S O) (expr_B_size e1)) (expr_B_size e2)
  | Or_b (e1, e2) -> plus (plus (S O) (expr_B_size e1)) (expr_B_size e2)

(** val neg_propagate : expr_b -> bool -> expr_b **)

let rec neg_propagate b n =
  match b with
    | True_b -> (match n with
                   | True -> Neg_b b
                   | False -> b)
    | Eq_b (e, e0) -> (match n with
                         | True -> Neg_b b
                         | False -> b)
    | Neq_b (e, e0) -> (match n with
                          | True -> Neg_b b
                          | False -> b)
    | Ge_b (e, e0) -> (match n with
                         | True -> Neg_b b
                         | False -> b)
    | Gt_b (e, e0) -> (match n with
                         | True -> Neg_b b
                         | False -> b)
    | Neg_b b1 -> neg_propagate b1 (negb n)
    | And_b (b1, b2) ->
        (match n with
           | True -> Or_b ((neg_propagate b1 True), (neg_propagate b2 True))
           | False -> And_b ((neg_propagate b1 False),
               (neg_propagate b2 False)))
    | Or_b (b1, b2) ->
        (match n with
           | True -> And_b ((neg_propagate b1 True), (neg_propagate b2 True))
           | False -> Or_b ((neg_propagate b1 False),
               (neg_propagate b2 False)))

type constraint0 = expr

type andlist = constraint0 list

(** val andlist_plus_andlist : andlist -> andlist -> andlist **)

let andlist_plus_andlist c1 c2 =
  app c1 c2

type orlist = andlist list

(** val orlist_plus_orlist : orlist -> orlist -> orlist **)

let orlist_plus_orlist d1 d2 =
  app d1 d2

(** val andlist_mult_orlist : andlist -> orlist -> orlist **)

let rec andlist_mult_orlist c = function
  | Nil -> Nil
  | Cons (hd, tl) ->
      orlist_plus_orlist (Cons ((andlist_plus_andlist c hd), Nil))
        (andlist_mult_orlist c tl)

(** val orlist_mult_orlist : orlist -> orlist -> orlist **)

let rec orlist_mult_orlist d1 d2 =
  match d1 with
    | Nil -> Nil
    | Cons (hd, tl) ->
        orlist_plus_orlist (andlist_mult_orlist hd d2)
          (orlist_mult_orlist tl d2)

(** val disj_nf : expr_b -> orlist **)

let rec disj_nf = function
  | True_b -> Cons ((Cons ((nat_e O), Nil)), Nil)
  | Eq_b (e1, e2) -> Cons ((Cons ((Min_e (e1, e2)), (Cons ((Min_e (e2, e1)),
      Nil)))), Nil)
  | Neq_b (e1, e2) -> Cons ((Cons ((Min_e ((Add_e (e1, 
      (nat_e (S O)))), e2)), Nil)), (Cons ((Cons ((Min_e ((Add_e (e2,
      (nat_e (S O)))), e1)), Nil)), Nil)))
  | Ge_b (e1, e2) -> Cons ((Cons ((Min_e (e2, e1)), Nil)), Nil)
  | Gt_b (e1, e2) -> Cons ((Cons ((Min_e ((Add_e (e2, 
      (nat_e (S O)))), e1)), Nil)), Nil)
  | Neg_b b1 ->
      (match b1 with
         | True_b -> Cons ((Cons ((nat_e (S O)), Nil)), Nil)
         | Eq_b (e1, e2) -> Cons ((Cons ((Min_e ((Add_e (e1, 
             (nat_e (S O)))), e2)), Nil)), (Cons ((Cons ((Min_e ((Add_e (e2,
             (nat_e (S O)))), e1)), Nil)), Nil)))
         | Neq_b (e1, e2) -> Cons ((Cons ((Min_e (e1, e2)), (Cons ((Min_e
             (e2, e1)), Nil)))), Nil)
         | Ge_b (e1, e2) -> Cons ((Cons ((Min_e ((Add_e (e1, 
             (nat_e (S O)))), e2)), Nil)), Nil)
         | Gt_b (e1, e2) -> Cons ((Cons ((Min_e (e1, e2)), Nil)), Nil)
         | Neg_b e -> Nil
         | And_b (e, e0) -> Nil
         | Or_b (e, e0) -> Nil)
  | And_b (e1, e2) -> orlist_mult_orlist (disj_nf e1) (disj_nf e2)
  | Or_b (e1, e2) -> orlist_plus_orlist (disj_nf e1) (disj_nf e2)

(** val expr_b2constraints : expr_b -> orlist **)

let expr_b2constraints b =
  disj_nf (neg_propagate b False)

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

(** val simpl_expr' : expr -> expr **)

let rec simpl_expr' e = match e with
  | Var_e v0 -> Var_e v0
  | Int_e z0 -> Int_e z0
  | Add_e (e1, e2) ->
      (match expr_compute (simpl_expr' e1) with
         | Some e1' ->
             (match zeq_bool e1' Z0 with
                | True ->
                    (match expr_compute (simpl_expr' e2) with
                       | Some e2' ->
                           (match zeq_bool e2' Z0 with
                              | True -> Int_e Z0
                              | False -> Int_e e2')
                       | None -> e2)
                | False ->
                    (match expr_compute (simpl_expr' e2) with
                       | Some e2' ->
                           (match zeq_bool e2' Z0 with
                              | True -> Int_e e1'
                              | False -> Int_e (zplus e1' e2'))
                       | None -> Add_e ((Int_e e1'), e2)))
         | None ->
             (match expr_compute (simpl_expr' e2) with
                | Some e2' ->
                    (match zeq_bool e2' Z0 with
                       | True -> e1
                       | False -> Add_e (e1, (Int_e e2')))
                | None -> e))
  | Min_e (e1, e2) ->
      (match expr_compute (simpl_expr' e1) with
         | Some e1' ->
             (match zeq_bool e1' Z0 with
                | True ->
                    (match expr_compute (simpl_expr' e2) with
                       | Some e2' ->
                           (match zeq_bool e2' Z0 with
                              | True -> Int_e Z0
                              | False -> Int_e (zopp e2'))
                       | None -> Min_e ((Int_e Z0), e2))
                | False ->
                    (match expr_compute (simpl_expr' e2) with
                       | Some e2' ->
                           (match zeq_bool e2' Z0 with
                              | True -> Int_e e1'
                              | False -> Int_e (zminus e1' e2'))
                       | None -> Min_e ((Int_e e1'), e2)))
         | None ->
             (match expr_compute (simpl_expr' e2) with
                | Some e2' ->
                    (match zeq_bool e2' Z0 with
                       | True -> e1
                       | False -> Min_e (e1, (Int_e e2')))
                | None -> e))
  | Mul_e (e1, e2) ->
      (match expr_compute (simpl_expr' e1) with
         | Some e1' ->
             (match zeq_bool e1' Z0 with
                | True -> Int_e Z0
                | False ->
                    (match zeq_bool e1' (Zpos XH) with
                       | True ->
                           (match expr_compute (simpl_expr' e2) with
                              | Some e2' ->
                                  (match zeq_bool e2' Z0 with
                                     | True -> Int_e Z0
                                     | False -> Int_e e2')
                              | None -> e2)
                       | False ->
                           (match expr_compute (simpl_expr' e2) with
                              | Some e2' ->
                                  (match zeq_bool e2' Z0 with
                                     | True -> Int_e Z0
                                     | False ->
                                         (match zeq_bool e2' (Zpos XH) with
                                            | True -> Int_e e1'
                                            | False -> Int_e (zmult e1' e2')))
                              | None -> Mul_e ((Int_e e1'), e2))))
         | None ->
             (match expr_compute (simpl_expr' e2) with
                | Some e2' ->
                    (match zeq_bool e2' Z0 with
                       | True -> Int_e Z0
                       | False ->
                           (match zeq_bool e2' (Zpos XH) with
                              | True -> e1
                              | False -> Mul_e (e1, (Int_e e2'))))
                | None -> e))
  | Div_e (e0, e1) -> e
  | Mod_e (e0, e1) -> e

(** val expr_deep : expr -> nat **)

let rec expr_deep = function
  | Var_e v0 -> S O
  | Int_e v0 -> S O
  | Add_e (e1, e2) -> plus (S O) (max (expr_deep e1) (expr_deep e2))
  | Min_e (e1, e2) -> plus (S O) (max (expr_deep e1) (expr_deep e2))
  | Mul_e (e1, e2) -> plus (S O) (max (expr_deep e1) (expr_deep e2))
  | Div_e (e0, e1) -> S O
  | Mod_e (e0, e1) -> S O

(** val simpl_expr_fp : expr -> nat -> expr **)

let rec simpl_expr_fp e = function
  | O -> e
  | S n' ->
      (match e with
         | Var_e v0 -> Var_e v0
         | Int_e z0 -> Int_e z0
         | Add_e (e1, e2) ->
             simpl_expr' (Add_e ((simpl_expr_fp e1 n'),
               (simpl_expr_fp e2 n')))
         | Min_e (e1, e2) ->
             simpl_expr' (Min_e ((simpl_expr_fp e1 n'),
               (simpl_expr_fp e2 n')))
         | Mul_e (e1, e2) ->
             simpl_expr' (Mul_e ((simpl_expr_fp e1 n'),
               (simpl_expr_fp e2 n')))
         | Div_e (e0, e1) -> e
         | Mod_e (e0, e1) -> e)

(** val simpl_expr : expr -> expr **)

let simpl_expr e =
  simpl_expr_fp e (expr_deep e)

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
  | Nil -> simpl_expr c
  | Cons (hd, tl) ->
      let Pair (e1, e2) = expr_var_fact' c hd in
      simpl_expr (Add_e
        ((simpl_expr (Mul_e ((Var_e hd), (simpl_varlist_constraint e1 tl)))),
        (simpl_expr (simpl_varlist_constraint e2 tl))))

(** val simpl_constraint : constraint0 -> constraint0 **)

let simpl_constraint c =
  simpl_varlist_constraint c (expr_var c)

(** val simpl_expr_b : expr_b -> expr_b **)

let rec simpl_expr_b b = match b with
  | True_b -> b
  | Eq_b (e1, e2) -> Eq_b ((simpl_constraint e1), (simpl_constraint e2))
  | Neq_b (e1, e2) -> Neq_b ((simpl_constraint e1), (simpl_constraint e2))
  | Ge_b (e1, e2) -> Ge_b ((simpl_constraint e1), (simpl_constraint e2))
  | Gt_b (e1, e2) -> Gt_b ((simpl_constraint e1), (simpl_constraint e2))
  | Neg_b e -> Neg_b (simpl_expr_b e)
  | And_b (e1, e2) -> And_b ((simpl_expr_b e1), (simpl_expr_b e2))
  | Or_b (e1, e2) -> Or_b ((simpl_expr_b e1), (simpl_expr_b e2))

(** val simpl_andlist : andlist -> andlist **)

let rec simpl_andlist = function
  | Nil -> Nil
  | Cons (hd, tl) -> Cons ((simpl_constraint hd), (simpl_andlist tl))

(** val simpl_orlist : orlist -> orlist **)

let rec simpl_orlist = function
  | Nil -> Nil
  | Cons (hd, tl) -> Cons ((simpl_andlist hd), (simpl_orlist tl))

(** val expr_var_fact : expr -> nat -> (expr, expr) prod **)

let expr_var_fact e v0 =
  let Pair (e1, e2) = expr_var_fact' e v0 in
  Pair ((simpl_constraint e1), (simpl_constraint e2))

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
                   | True ->
                       simpl_constraint (Min_e ((Mul_e (e21, e12)), (Mul_e
                         (e11, e22))))
                   | False ->
                       (match match zlt_bool Z0 e11' with
                                | True -> zlt_bool e21' Z0
                                | False -> False with
                          | True ->
                              simpl_constraint (Min_e ((Mul_e (e11, e22)),
                                (Mul_e (e21, e12))))
                          | False -> simpl_constraint c2))
            | None -> simpl_constraint c2)
     | None -> simpl_constraint c2)

(** val elim_var_andlist' : constraint0 -> andlist -> andlist -> nat ->
                            andlist **)

let rec elim_var_andlist' c l l' v0 =
  match l with
    | Nil -> l'
    | Cons (hd, tl) ->
        (match inb beq_nat (expr_var (simpl_constraint hd)) v0 with
           | True ->
               elim_var_andlist' c tl (Cons ((elim_var_constraint c hd v0),
                 l')) v0
           | False -> elim_var_andlist' c tl l' v0)

(** val elim_var_andlist : andlist -> andlist -> nat -> andlist **)

let rec elim_var_andlist l l' v0 =
  match l with
    | Nil -> l'
    | Cons (hd, tl) ->
        (match inb beq_nat (expr_var (simpl_constraint hd)) v0 with
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
  | Nil -> simpl_orlist l
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

(** val expr_b_dp : expr_b -> bool **)

let expr_b_dp b =
  match eval_orlist
          (elim_varlist_orlist
            (simpl_orlist (expr_b2constraints (simpl_expr_b (Neg_b b))))
            (expr_B_var (simpl_expr_b b))) with
    | Some res -> negb res
    | None -> False

type pi = expr_b

type sigma =
  | Singl of expr * expr
  | Cell of expr
  | Emp
  | Star of sigma * sigma
  | Lst of expr * expr

type assrt = (pi, sigma) prod

type assrt0 = assrt list

(** val remove_empty_heap : pi -> sigma -> sigma **)

let rec remove_empty_heap pi0 sig0 = match sig0 with
  | Singl (e, e0) -> sig0
  | Cell e -> sig0
  | Emp -> sig0
  | Star (sig1, sig2) ->
      (match remove_empty_heap pi0 sig1 with
         | Singl (e, e0) ->
             (match remove_empty_heap pi0 sig2 with
                | Singl (e1, e2) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Cell e1 -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Emp -> remove_empty_heap pi0 sig1
                | Star (s, s0) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Lst (e1, e2) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2)))
         | Cell e ->
             (match remove_empty_heap pi0 sig2 with
                | Singl (e0, e1) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Cell e0 -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Emp -> remove_empty_heap pi0 sig1
                | Star (s, s0) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Lst (e0, e1) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2)))
         | Emp -> remove_empty_heap pi0 sig2
         | Star (s, s0) ->
             (match remove_empty_heap pi0 sig2 with
                | Singl (e, e0) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Cell e -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Emp -> remove_empty_heap pi0 sig1
                | Star (s1, s2) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Lst (e, e0) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2)))
         | Lst (e, e0) ->
             (match remove_empty_heap pi0 sig2 with
                | Singl (e1, e2) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Cell e1 -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Emp -> remove_empty_heap pi0 sig1
                | Star (s, s0) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))
                | Lst (e1, e2) -> Star ((remove_empty_heap pi0 sig1),
                    (remove_empty_heap pi0 sig2))))
  | Lst (e1, e2) ->
      (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e2)))) with
         | True -> Emp
         | False -> sig0)

(** val cell_in_sigma : pi -> sigma -> expr -> bool **)

let rec cell_in_sigma pi0 sig0 e =
  match sig0 with
    | Singl (e1, e2) -> expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e))))
    | Cell e1 -> expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e))))
    | Emp -> False
    | Star (s1, s2) ->
        (match cell_in_sigma pi0 s1 e with
           | True -> True
           | False -> cell_in_sigma pi0 s2 e)
    | Lst (e1, e2) ->
        (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e)))) with
           | True -> expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e2))))
           | False -> False)

(** val sigma_eq : pi -> sigma -> sigma -> bool **)

let sigma_eq pi0 sig1 sig2 =
  match sig1 with
    | Singl (e1, e2) ->
        (match sig2 with
           | Singl (e3, e4) ->
               (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e3)))) with
                  | True -> expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e2, e4))))
                  | False -> False)
           | Cell e3 -> expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e3))))
           | Emp -> False
           | Star (s, s0) -> False
           | Lst (e, e0) -> False)
    | Cell e1 ->
        (match sig2 with
           | Singl (e, e0) -> False
           | Cell e3 -> expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e3))))
           | Emp -> False
           | Star (s, s0) -> False
           | Lst (e, e0) -> False)
    | Emp ->
        (match sig2 with
           | Singl (e, e0) -> False
           | Cell e -> False
           | Emp -> True
           | Star (s, s0) -> False
           | Lst (e, e0) -> False)
    | Star (s, s0) -> False
    | Lst (e1, e2) ->
        (match sig2 with
           | Singl (e, e0) -> False
           | Cell e -> False
           | Emp -> False
           | Star (s, s0) -> False
           | Lst (e3, e4) ->
               (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e3)))) with
                  | True -> expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e2, e4))))
                  | False -> False))

(** val elim_common_cell : pi -> sigma -> sigma -> sigma -> (sigma, sigma)
                           prod option **)

let rec elim_common_cell pi0 sig1 remainder sig2 = match sig2 with
  | Singl (e, e0) ->
      (match sigma_eq pi0 sig1 sig2 with
         | True -> Some (Pair (Emp, Emp))
         | False ->
             (match sig1 with
                | Singl (e1, e2) ->
                    (match sig2 with
                       | Singl (e3, e4) -> None
                       | Cell e3 -> None
                       | Emp -> None
                       | Star (s, s0) -> None
                       | Lst (e3, e4) ->
                           (match match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b
                                          (e1, e3)))) with
                                    | True ->
                                        (match expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Neq_b (e1, e4)))) with
                                           | True ->
                                               expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Neq_b (e1, 
                                                 (nat_e O)))))
                                           | False -> False)
                                    | False -> False with
                              | True -> Some (Pair (Emp, (Star ((Cell (Add_e
                                  (e1, (nat_e (S O))))), (Lst (e2, e4))))))
                              | False -> None))
                | Cell e1 -> None
                | Emp ->
                    (match sig2 with
                       | Singl (e1, e2) -> Some (Pair (Emp, sig2))
                       | Cell e1 -> Some (Pair (Emp, sig2))
                       | Emp -> Some (Pair (Emp, sig2))
                       | Star (s, s0) -> Some (Pair (Emp, sig2))
                       | Lst (e3, e4) ->
                           (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e3,
                                    e4)))) with
                              | True -> Some (Pair (Emp, Emp))
                              | False -> Some (Pair (Emp, sig2))))
                | Star (s, s0) -> None
                | Lst (e11, e12) ->
                    (match sig2 with
                       | Singl (e1, e2) -> None
                       | Cell e1 -> None
                       | Emp -> None
                       | Star (s, s0) -> None
                       | Lst (e21, e22) ->
                           (match match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b
                                          (e11, e21)))) with
                                    | True ->
                                        (match expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Eq_b (e22, 
                                                 (nat_e O))))) with
                                           | True -> True
                                           | False ->
                                               cell_in_sigma pi0 remainder
                                                 e22)
                                    | False -> False with
                              | True -> Some (Pair (Emp, (Lst (e12, e22))))
                              | False -> None))))
  | Cell e ->
      (match sigma_eq pi0 sig1 sig2 with
         | True -> Some (Pair (Emp, Emp))
         | False ->
             (match sig1 with
                | Singl (e1, e2) ->
                    (match sig2 with
                       | Singl (e0, e3) -> None
                       | Cell e0 -> None
                       | Emp -> None
                       | Star (s, s0) -> None
                       | Lst (e3, e4) ->
                           (match match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b
                                          (e1, e3)))) with
                                    | True ->
                                        (match expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Neq_b (e1, e4)))) with
                                           | True ->
                                               expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Neq_b (e1, 
                                                 (nat_e O)))))
                                           | False -> False)
                                    | False -> False with
                              | True -> Some (Pair (Emp, (Star ((Cell (Add_e
                                  (e1, (nat_e (S O))))), (Lst (e2, e4))))))
                              | False -> None))
                | Cell e0 -> None
                | Emp ->
                    (match sig2 with
                       | Singl (e0, e1) -> Some (Pair (Emp, sig2))
                       | Cell e0 -> Some (Pair (Emp, sig2))
                       | Emp -> Some (Pair (Emp, sig2))
                       | Star (s, s0) -> Some (Pair (Emp, sig2))
                       | Lst (e3, e4) ->
                           (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e3,
                                    e4)))) with
                              | True -> Some (Pair (Emp, Emp))
                              | False -> Some (Pair (Emp, sig2))))
                | Star (s, s0) -> None
                | Lst (e11, e12) ->
                    (match sig2 with
                       | Singl (e0, e1) -> None
                       | Cell e0 -> None
                       | Emp -> None
                       | Star (s, s0) -> None
                       | Lst (e21, e22) ->
                           (match match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b
                                          (e11, e21)))) with
                                    | True ->
                                        (match expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Eq_b (e22, 
                                                 (nat_e O))))) with
                                           | True -> True
                                           | False ->
                                               cell_in_sigma pi0 remainder
                                                 e22)
                                    | False -> False with
                              | True -> Some (Pair (Emp, (Lst (e12, e22))))
                              | False -> None))))
  | Emp ->
      (match sigma_eq pi0 sig1 sig2 with
         | True -> Some (Pair (Emp, Emp))
         | False ->
             (match sig1 with
                | Singl (e1, e2) ->
                    (match sig2 with
                       | Singl (e, e0) -> None
                       | Cell e -> None
                       | Emp -> None
                       | Star (s, s0) -> None
                       | Lst (e3, e4) ->
                           (match match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b
                                          (e1, e3)))) with
                                    | True ->
                                        (match expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Neq_b (e1, e4)))) with
                                           | True ->
                                               expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Neq_b (e1, 
                                                 (nat_e O)))))
                                           | False -> False)
                                    | False -> False with
                              | True -> Some (Pair (Emp, (Star ((Cell (Add_e
                                  (e1, (nat_e (S O))))), (Lst (e2, e4))))))
                              | False -> None))
                | Cell e -> None
                | Emp ->
                    (match sig2 with
                       | Singl (e, e0) -> Some (Pair (Emp, sig2))
                       | Cell e -> Some (Pair (Emp, sig2))
                       | Emp -> Some (Pair (Emp, sig2))
                       | Star (s, s0) -> Some (Pair (Emp, sig2))
                       | Lst (e3, e4) ->
                           (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e3,
                                    e4)))) with
                              | True -> Some (Pair (Emp, Emp))
                              | False -> Some (Pair (Emp, sig2))))
                | Star (s, s0) -> None
                | Lst (e11, e12) ->
                    (match sig2 with
                       | Singl (e, e0) -> None
                       | Cell e -> None
                       | Emp -> None
                       | Star (s, s0) -> None
                       | Lst (e21, e22) ->
                           (match match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b
                                          (e11, e21)))) with
                                    | True ->
                                        (match expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Eq_b (e22, 
                                                 (nat_e O))))) with
                                           | True -> True
                                           | False ->
                                               cell_in_sigma pi0 remainder
                                                 e22)
                                    | False -> False with
                              | True -> Some (Pair (Emp, (Lst (e12, e22))))
                              | False -> None))))
  | Star (sig21, sig22) ->
      (match elim_common_cell pi0 sig1 remainder sig21 with
         | Some p ->
             let Pair (sig1', sig2') = p in
             Some (Pair (sig1',
             (remove_empty_heap pi0 (Star (sig2', sig22)))))
         | None ->
             (match elim_common_cell pi0 sig1 remainder sig22 with
                | Some p ->
                    let Pair (sig1', sig2') = p in
                    Some (Pair (sig1',
                    (remove_empty_heap pi0 (Star (sig21, sig2')))))
                | None -> None))
  | Lst (e, e0) ->
      (match sigma_eq pi0 sig1 sig2 with
         | True -> Some (Pair (Emp, Emp))
         | False ->
             (match sig1 with
                | Singl (e1, e2) ->
                    (match sig2 with
                       | Singl (e3, e4) -> None
                       | Cell e3 -> None
                       | Emp -> None
                       | Star (s, s0) -> None
                       | Lst (e3, e4) ->
                           (match match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b
                                          (e1, e3)))) with
                                    | True ->
                                        (match expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Neq_b (e1, e4)))) with
                                           | True ->
                                               expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Neq_b (e1, 
                                                 (nat_e O)))))
                                           | False -> False)
                                    | False -> False with
                              | True -> Some (Pair (Emp, (Star ((Cell (Add_e
                                  (e1, (nat_e (S O))))), (Lst (e2, e4))))))
                              | False -> None))
                | Cell e1 -> None
                | Emp ->
                    (match sig2 with
                       | Singl (e1, e2) -> Some (Pair (Emp, sig2))
                       | Cell e1 -> Some (Pair (Emp, sig2))
                       | Emp -> Some (Pair (Emp, sig2))
                       | Star (s, s0) -> Some (Pair (Emp, sig2))
                       | Lst (e3, e4) ->
                           (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e3,
                                    e4)))) with
                              | True -> Some (Pair (Emp, Emp))
                              | False -> Some (Pair (Emp, sig2))))
                | Star (s, s0) -> None
                | Lst (e11, e12) ->
                    (match sig2 with
                       | Singl (e1, e2) -> None
                       | Cell e1 -> None
                       | Emp -> None
                       | Star (s, s0) -> None
                       | Lst (e21, e22) ->
                           (match match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b
                                          (e11, e21)))) with
                                    | True ->
                                        (match expr_b_dp (Or_b ((Neg_b pi0),
                                                 (Eq_b (e22, 
                                                 (nat_e O))))) with
                                           | True -> True
                                           | False ->
                                               cell_in_sigma pi0 remainder
                                                 e22)
                                    | False -> False with
                              | True -> Some (Pair (Emp, (Lst (e12, e22))))
                              | False -> None))))

(** val elim_common_subheap : pi -> sigma -> sigma -> sigma -> (sigma, sigma)
                              prod option **)

let rec elim_common_subheap pi0 sig1 sig2 remainder =
  match sig1 with
    | Singl (e, e0) -> elim_common_cell pi0 sig1 remainder sig2
    | Cell e -> elim_common_cell pi0 sig1 remainder sig2
    | Emp -> elim_common_cell pi0 sig1 remainder sig2
    | Star (sig11, sig12) ->
        (match elim_common_subheap pi0 sig11 sig2 (Star (sig12, remainder)) with
           | Some p ->
               let Pair (sig11', sig12') = p in
               Some (Pair ((remove_empty_heap pi0 (Star (sig11', sig12))),
               sig12'))
           | None -> None)
    | Lst (e, e0) -> elim_common_cell pi0 sig1 remainder sig2

(** val star_assoc_left : sigma -> sigma -> sigma **)

let rec star_assoc_left sig1 sig2 =
  match sig1 with
    | Singl (e, e0) ->
        (match sig2 with
           | Singl (e1, e2) -> Star (sig2, sig1)
           | Cell e1 -> Star (sig2, sig1)
           | Emp -> sig1
           | Star (s, s0) -> Star (sig2, sig1)
           | Lst (e1, e2) -> Star (sig2, sig1))
    | Cell e ->
        (match sig2 with
           | Singl (e0, e1) -> Star (sig2, sig1)
           | Cell e0 -> Star (sig2, sig1)
           | Emp -> sig1
           | Star (s, s0) -> Star (sig2, sig1)
           | Lst (e0, e1) -> Star (sig2, sig1))
    | Emp ->
        (match sig2 with
           | Singl (e, e0) -> Star (sig2, sig1)
           | Cell e -> Star (sig2, sig1)
           | Emp -> sig1
           | Star (s, s0) -> Star (sig2, sig1)
           | Lst (e, e0) -> Star (sig2, sig1))
    | Star (sig11, sig12) -> star_assoc_left sig12 (Star (sig2, sig11))
    | Lst (e, e0) ->
        (match sig2 with
           | Singl (e1, e2) -> Star (sig2, sig1)
           | Cell e1 -> Star (sig2, sig1)
           | Emp -> sig1
           | Star (s, s0) -> Star (sig2, sig1)
           | Lst (e1, e2) -> Star (sig2, sig1))

(** val star_com : sigma -> sigma **)

let star_com sig0 = match sig0 with
  | Singl (e, e0) -> sig0
  | Cell e -> sig0
  | Emp -> sig0
  | Star (sig1, sig2) -> Star (sig2, sig1)
  | Lst (e, e0) -> sig0

(** val rearrange_elim_common_subheap : pi -> sigma -> sigma -> (sigma,
                                        sigma) prod **)

let rearrange_elim_common_subheap pi0 sig1 sig2 =
  match elim_common_subheap pi0 sig1 sig2 Emp with
    | Some s -> s
    | None -> Pair
        ((remove_empty_heap pi0 (star_com (star_assoc_left sig1 Emp))), sig2)

(** val elim_common_subheap_iterate : pi -> sigma -> sigma -> nat -> (sigma,
                                      sigma) prod **)

let rec elim_common_subheap_iterate pi0 sig1 sig2 = function
  | O -> Pair (sig1, sig2)
  | S n ->
      let Pair (sig1', sig2') = rearrange_elim_common_subheap pi0 sig1 sig2
      in
      elim_common_subheap_iterate pi0 sig1' sig2' n

(** val sigma_size : sigma -> nat **)

let rec sigma_size = function
  | Singl (e1, e2) -> S O
  | Cell e1 -> S O
  | Emp -> S O
  | Star (s1, s2) -> plus (sigma_size s1) (sigma_size s2)
  | Lst (e1, e2) -> S (S (S O))

type 'a result =
  | Good
  | Error of 'a

(** val sigma_impl : pi -> sigma -> sigma -> (sigma, sigma) prod result **)

let sigma_impl pi0 sig1 sig2 =
  let Pair (s, s0) =
    elim_common_subheap_iterate pi0 sig1 sig2
      (mult (plus (sigma_size sig1) (sigma_size sig2)) (S (S O)))
  in
  (match s with
     | Singl (e0, e1) -> Error
         (elim_common_subheap_iterate pi0 sig1 sig2
           (mult (plus (sigma_size sig1) (sigma_size sig2)) (S (S O))))
     | Cell e0 -> Error
         (elim_common_subheap_iterate pi0 sig1 sig2
           (mult (plus (sigma_size sig1) (sigma_size sig2)) (S (S O))))
     | Emp ->
         (match s0 with
            | Singl (e0, e1) -> Error
                (elim_common_subheap_iterate pi0 sig1 sig2
                  (mult (plus (sigma_size sig1) (sigma_size sig2)) (S (S O))))
            | Cell e0 -> Error
                (elim_common_subheap_iterate pi0 sig1 sig2
                  (mult (plus (sigma_size sig1) (sigma_size sig2)) (S (S O))))
            | Emp -> Good
            | Star (s1, s2) -> Error
                (elim_common_subheap_iterate pi0 sig1 sig2
                  (mult (plus (sigma_size sig1) (sigma_size sig2)) (S (S O))))
            | Lst (e0, e1) -> Error
                (elim_common_subheap_iterate pi0 sig1 sig2
                  (mult (plus (sigma_size sig1) (sigma_size sig2)) (S (S O)))))
     | Star (s1, s2) -> Error
         (elim_common_subheap_iterate pi0 sig1 sig2
           (mult (plus (sigma_size sig1) (sigma_size sig2)) (S (S O))))
     | Lst (e0, e1) -> Error
         (elim_common_subheap_iterate pi0 sig1 sig2
           (mult (plus (sigma_size sig1) (sigma_size sig2)) (S (S O)))))

(** val frag_entail_fun : assrt -> assrt -> (assrt, assrt) prod result **)

let frag_entail_fun a1 a2 =
  let Pair (pi1, sig1) = a1 in
  let Pair (pi2, sig2) = a2 in
  (match expr_b_dp (Neg_b pi1) with
     | True -> Good
     | False ->
         (match sigma_impl pi1 sig1 sig2 with
            | Good ->
                (match expr_b_dp (Or_b ((Neg_b pi1), pi2)) with
                   | True -> Good
                   | False -> Error (Pair ((Pair (pi1, Emp)), (Pair (pi2,
                       Emp)))))
            | Error p ->
                let Pair (s1, s2) = p in
                Error (Pair ((Pair (pi1, s1)), (Pair (pi2, s2))))))

(** val compute_constraint_cell : pi -> sigma -> sigma -> pi **)

let compute_constraint_cell pi0 sig1 sig2 =
  match sig1 with
    | Singl (e1, e2) ->
        (match sig2 with
           | Singl (e3, e4) ->
               (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e3)))) with
                  | True -> pi0
                  | False -> And_b (pi0, (Neq_b (e1, e3))))
           | Cell e3 ->
               (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e3)))) with
                  | True -> pi0
                  | False -> And_b (pi0, (Neq_b (e1, e3))))
           | Emp -> pi0
           | Star (s, s0) -> pi0
           | Lst (e3, e4) ->
               (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e3, e4)))) with
                  | True ->
                      (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e3)))) with
                         | True -> pi0
                         | False -> And_b (pi0, (Neq_b (e1, e3))))
                  | False -> pi0))
    | Cell e1 ->
        (match sig2 with
           | Singl (e3, e4) ->
               (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e3)))) with
                  | True -> pi0
                  | False -> And_b (pi0, (Neq_b (e1, e3))))
           | Cell e3 ->
               (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e3)))) with
                  | True -> pi0
                  | False -> And_b (pi0, (Neq_b (e1, e3))))
           | Emp -> pi0
           | Star (s, s0) -> pi0
           | Lst (e3, e4) ->
               (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e3, e4)))) with
                  | True ->
                      (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e3)))) with
                         | True -> pi0
                         | False -> And_b (pi0, (Neq_b (e1, e3))))
                  | False -> pi0))
    | Emp -> pi0
    | Star (s, s0) -> pi0
    | Lst (e1, e2) ->
        (match sig2 with
           | Singl (e3, e4) ->
               (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e2)))) with
                  | True ->
                      (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e3)))) with
                         | True -> pi0
                         | False -> And_b (pi0, (Neq_b (e1, e3))))
                  | False -> pi0)
           | Cell e3 ->
               (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e2)))) with
                  | True ->
                      (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e3)))) with
                         | True -> pi0
                         | False -> And_b (pi0, (Neq_b (e1, e3))))
                  | False -> pi0)
           | Emp -> pi0
           | Star (s, s0) -> pi0
           | Lst (e3, e4) ->
               (match match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e2)))) with
                        | True ->
                            expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e3, e4))))
                        | False -> False with
                  | True ->
                      (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, e3)))) with
                         | True -> pi0
                         | False -> And_b (pi0, (Neq_b (e1, e3))))
                  | False -> pi0))

(** val compute_constraint_cell_sigma : pi -> sigma -> sigma -> pi **)

let rec compute_constraint_cell_sigma pi0 sig1 sig2 = match sig2 with
  | Singl (e, e0) -> compute_constraint_cell pi0 sig1 sig2
  | Cell e -> compute_constraint_cell pi0 sig1 sig2
  | Emp -> compute_constraint_cell pi0 sig1 sig2
  | Star (sig21, sig22) ->
      compute_constraint_cell_sigma
        (compute_constraint_cell_sigma pi0 sig1 sig21) sig1 sig22
  | Lst (e, e0) -> compute_constraint_cell pi0 sig1 sig2

(** val compute_constraints' : pi -> sigma -> pi **)

let rec compute_constraints' pi0 = function
  | Singl (e, e0) -> pi0
  | Cell e -> pi0
  | Emp -> pi0
  | Star (sig1, sig2) ->
      compute_constraints' (compute_constraint_cell_sigma pi0 sig2 sig1) sig1
  | Lst (e, e0) -> pi0

(** val compute_constraints : pi -> sigma -> pi **)

let compute_constraints pi0 sig0 =
  compute_constraints' pi0 (star_assoc_left sig0 Emp)

(** val cell_loc_not_null : pi -> sigma -> pi **)

let rec cell_loc_not_null pi0 = function
  | Singl (e1, e2) ->
      (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, (nat_e O))))) with
         | True -> pi0
         | False -> And_b (pi0, (Neq_b (e1, (nat_e O)))))
  | Cell e1 ->
      (match expr_b_dp (Or_b ((Neg_b pi0), (Neq_b (e1, (nat_e O))))) with
         | True -> pi0
         | False -> And_b (pi0, (Neq_b (e1, (nat_e O)))))
  | Emp -> pi0
  | Star (s1, s2) -> cell_loc_not_null (cell_loc_not_null pi0 s1) s2
  | Lst (e1, e2) -> pi0

(** val assrt_entail_fun : assrt -> assrt -> (assrt, assrt) prod result **)

let assrt_entail_fun a1 a2 =
  let Pair (pi1, sig1) = a1 in
  frag_entail_fun (Pair
    ((compute_constraints (cell_loc_not_null pi1 sig1) sig1), sig1)) a2

(** val orassrt_impl_Assrt1 : assrt -> assrt0 -> (assrt, assrt) prod list ->
                              (assrt, assrt) prod list result **)

let rec orassrt_impl_Assrt1 a a0 l =
  match a0 with
    | Nil -> Error l
    | Cons (hd, tl) ->
        (match assrt_entail_fun a hd with
           | Good -> Good
           | Error e -> orassrt_impl_Assrt1 a tl (Cons (e, l)))

(** val orpi : assrt list -> expr_b **)

let rec orpi = function
  | Nil -> Neg_b True_b
  | Cons (a, tl) -> let Pair (pi0, sig0) = a in Or_b (pi0, (orpi tl))

(** val orassrt_impl_Assrt2 : assrt -> assrt0 -> (assrt, assrt) prod list ->
                              (assrt, assrt) prod list result **)

let rec orassrt_impl_Assrt2 a a0 l =
  match a0 with
    | Nil -> Error l
    | Cons (a1, tl) ->
        let Pair (pi0, sig0) = a1 in
        let Pair (pi', sig') = a in
        (match sigma_impl (And_b (pi', pi0)) sig' sig0 with
           | Good ->
               (match tl with
                  | Nil -> Good
                  | Cons (a2, l0) -> orassrt_impl_Assrt2 a tl l)
           | Error p ->
               let Pair (s1, s2) = p in
               Error (Cons ((Pair ((Pair (pi', s1)), (Pair (pi0, s2)))), l)))

(** val entail_fun : assrt -> assrt0 -> (assrt, assrt) prod list -> (assrt,
                     assrt) prod list result **)

let entail_fun a a0 l =
  let Pair (pi0, sig0) = a in
  (match expr_b_dp (Or_b ((Neg_b pi0), (orpi a0))) with
     | True ->
         (match orassrt_impl_Assrt2 a a0 Nil with
            | Good -> Good
            | Error e -> orassrt_impl_Assrt1 a a0 Nil)
     | False -> orassrt_impl_Assrt1 a a0 Nil)

type wpAssrt =
  | WpElt of assrt0
  | WpSubst of (Coq_var.v, expr) prod list * wpAssrt
  | WpLookup of Coq_var.v * expr * wpAssrt
  | WpMutation of expr * expr * wpAssrt
  | WpIf of expr_b * wpAssrt * wpAssrt

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
    | Emp -> Emp
    | Star (s1, s2) -> Star ((subst_Sigma s1 x e), (subst_Sigma s2 x e))
    | Lst (e1, e2) -> Lst ((subst_e e1 (Var_e x) e),
        (subst_e e2 (Var_e x) e))

(** val subst_assrt : assrt -> Coq_var.v -> expr -> assrt **)

let subst_assrt a x e =
  let Pair (pi0, sigm) = a in
  Pair ((subst_b pi0 (Var_e x) e), (subst_Sigma sigm x e))

(** val subst_Assrt : assrt0 -> Coq_var.v -> expr -> assrt0 **)

let rec subst_Assrt a x e =
  match a with
    | Nil -> Nil
    | Cons (hd, tl) -> Cons ((subst_assrt hd x e), (subst_Assrt tl x e))

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

(** val subst_Assrt_lst : (Coq_var.v, expr) prod list -> assrt0 -> assrt0 **)

let rec subst_Assrt_lst l a =
  match l with
    | Nil -> a
    | Cons (p, tl) ->
        let Pair (x, e) = p in subst_Assrt_lst tl (subst_Assrt a x e)

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
    | Emp -> O
    | Star (s1, s2) -> max (var_max_Sigma s1) (var_max_Sigma s2)
    | Lst (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
  
  (** val var_max_assrt : assrt -> Coq_var.v **)
  
  let var_max_assrt = function
    | Pair (pi0, sigm) -> max (var_max_expr_b pi0) (var_max_Sigma sigm)
  
  (** val var_max_Assrt : assrt0 -> Coq_var.v **)
  
  let rec var_max_Assrt = function
    | Nil -> O
    | Cons (hd, tl) -> max (var_max_assrt hd) (var_max_Assrt tl)
  
  (** val var_max_lst : (Coq_var.v, expr) prod list -> Coq_var.v **)
  
  let rec var_max_lst = function
    | Nil -> O
    | Cons (p, tl) ->
        let Pair (v0, e) = p in
        max (max v0 (var_max_expr e)) (var_max_lst tl)
  
  (** val var_max_wpAssrt : wpAssrt -> Coq_var.v **)
  
  let rec var_max_wpAssrt = function
    | WpElt a1 -> var_max_Assrt a1
    | WpSubst (l, l0) -> max (var_max_lst l) (var_max_wpAssrt l0)
    | WpLookup (x, e, l) -> max (max x (var_max_expr e)) (var_max_wpAssrt l)
    | WpMutation (e1, e2, l) ->
        max (max (var_max_expr e1) (var_max_expr e2)) (var_max_wpAssrt l)
    | WpIf (b, l1, l2) ->
        max (max (var_max_wpAssrt l1) (var_max_wpAssrt l2))
          (var_max_expr_b b)
  
  (** val var_max_cmd : cmd -> Coq_var.v **)
  
  let rec var_max_cmd = function
    | Skip -> O
    | Assign (x, e) -> max (var_max_expr e) x
    | Lookup (x, e) -> max (var_max_expr e) x
    | Mutation (e1, e2) -> max (var_max_expr e1) (var_max_expr e2)
    | Malloc (x, e) -> max (var_max_expr e) x
    | Free e -> var_max_expr e
    | While (b, c') -> max (var_max_expr_b b) (var_max_cmd c')
    | Seq (c1, c2) -> max (var_max_cmd c1) (var_max_cmd c2)
    | Ifte (b, c1, c2) ->
        max (max (var_max_cmd c1) (var_max_cmd c2)) (var_max_expr_b b)
 end

(** val triple_vfresh : assrt -> wpAssrt -> nat **)

let triple_vfresh a l =
  plus (max (Fresh.var_max_assrt a) (Fresh.var_max_wpAssrt l)) (S O)

(** val tritra_step' : pi -> sigma -> wpAssrt -> ((pi, sigma) prod, wpAssrt)
                       prod list option **)

let tritra_step' pi0 sig0 a = match a with
  | WpElt l ->
      (match entail_fun (Pair (pi0, sig0)) l Nil with
         | Good -> Some Nil
         | Error x -> None)
  | WpSubst (l, l0) ->
      (match l0 with
         | WpElt l' -> Some (Cons ((Pair ((Pair (pi0, sig0)), (WpElt
             (subst_Assrt_lst l l')))), Nil))
         | WpSubst (l', l'0) -> Some (Cons ((Pair ((Pair (pi0, sig0)),
             (WpSubst ((app l' l), l'0)))), Nil))
         | WpLookup (x, e, l') ->
             (match sig0 with
                | Singl (e1, e2) -> Some (Cons ((Pair ((Pair (pi0, (Star
                    (Emp, sig0)))), a)), Nil))
                | Cell e1 -> Some (Cons ((Pair ((Pair (pi0, (Star (Emp,
                    sig0)))), a)), Nil))
                | Emp -> Some (Cons ((Pair ((Pair (pi0,
                    (remove_empty_heap pi0
                      (star_assoc_left (star_com sig0) Emp)))), a)), Nil))
                | Star (s1, s) ->
                    (match s with
                       | Singl (e1, e2) ->
                           (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1,
                                    (subst_e_lst l e))))) with
                              | True ->
                                  let x' =
                                    plus
                                      (max
                                        (max (Fresh.var_max_lst l)
                                          (Fresh.var_max_wpAssrt l')) x) (S
                                      O)
                                  in
                                  Some (Cons ((Pair ((Pair (pi0, sig0)),
                                  (WpSubst ((Cons ((Pair (x, (Var_e x'))),
                                  (app l (Cons ((Pair (x', e2)), Nil))))),
                                  l')))), Nil))
                              | False -> Some (Cons ((Pair ((Pair (pi0,
                                  (remove_empty_heap pi0
                                    (star_assoc_left (star_com sig0) Emp)))),
                                  a)), Nil)))
                       | Cell e1 ->
                           (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1,
                                    (subst_e_lst l e))))) with
                              | True ->
                                  let x' =
                                    plus
                                      (max
                                        (max (Fresh.var_max_lst l)
                                          (Fresh.var_max_wpAssrt l')) x) (S
                                      O)
                                  in
                                  let x'' =
                                    plus
                                      (max
                                        (Fresh.var_max_assrt (Pair (pi0,
                                          sig0))) (Fresh.var_max_wpAssrt a))
                                      (S O)
                                  in
                                  Some (Cons ((Pair ((Pair (pi0, (Star (s1,
                                  (Singl (e1, (Var_e x''))))))), (WpSubst
                                  ((Cons ((Pair (x, (Var_e x'))),
                                  (app l (Cons ((Pair (x', (Var_e x''))),
                                    Nil))))), l')))), Nil))
                              | False -> Some (Cons ((Pair ((Pair (pi0,
                                  (remove_empty_heap pi0
                                    (star_assoc_left (star_com sig0) Emp)))),
                                  a)), Nil)))
                       | Emp -> Some (Cons ((Pair ((Pair (pi0,
                           (remove_empty_heap pi0
                             (star_assoc_left (star_com sig0) Emp)))), a)),
                           Nil))
                       | Star (s0, s2) -> Some (Cons ((Pair ((Pair (pi0,
                           (remove_empty_heap pi0
                             (star_assoc_left (star_com sig0) Emp)))), a)),
                           Nil))
                       | Lst (e1, e2) ->
                           (match expr_b_dp (Or_b ((Neg_b pi0), (And_b
                                    ((Neq_b (e1, e2)), (Eq_b (e1,
                                    (subst_e_lst l e))))))) with
                              | True ->
                                  let x' = triple_vfresh (Pair (pi0, sig0)) a
                                  in
                                  Some (Cons ((Pair ((Pair ((And_b ((And_b
                                  (pi0, (Neq_b (e1, (Var_e x'))))), (Eq_b
                                  ((Var_e x'), (nat_e O))))), (Star ((Star
                                  (s1, (Star ((Lst ((Var_e x'), e2)), (Cell
                                  (Add_e (e1, (nat_e (S O))))))))), (Singl
                                  (e1, (Var_e x'))))))), a)), (Cons ((Pair
                                  ((Pair ((And_b ((And_b (pi0, (Neq_b (e1,
                                  (Var_e x'))))), (Neq_b ((Var_e x'),
                                  (nat_e O))))), (Star ((Star (s1, (Star
                                  ((Lst ((Var_e x'), e2)), (Cell (Add_e (e1,
                                  (nat_e (S O))))))))), (Singl (e1, (Var_e
                                  x'))))))), a)), Nil))))
                              | False ->
                                  (match expr_b_dp (Or_b ((Neg_b pi0), (And_b
                                           ((Neq_b (e1, e2)), (Eq_b ((Add_e
                                           (e1, (nat_e (S O)))),
                                           (subst_e_lst l e))))))) with
                                     | True ->
                                         let x' =
                                           triple_vfresh (Pair (pi0, sig0)) a
                                         in
                                         Some (Cons ((Pair ((Pair ((And_b
                                         ((And_b (pi0, (Neq_b (e1, (Var_e
                                         x'))))), (Eq_b ((Var_e x'),
                                         (nat_e O))))), (Star ((Star (s1,
                                         (Star ((Lst ((Var_e x'), e2)),
                                         (Singl (e1, (Var_e x'))))))), (Cell
                                         (Add_e (e1, 
                                         (nat_e (S O))))))))), a)), (Cons
                                         ((Pair ((Pair ((And_b ((And_b (pi0,
                                         (Neq_b (e1, (Var_e x'))))), (Neq_b
                                         ((Var_e x'), 
                                         (nat_e O))))), (Star ((Star (s1,
                                         (Star ((Lst ((Var_e x'), e2)),
                                         (Singl (e1, (Var_e x'))))))), (Cell
                                         (Add_e (e1, 
                                         (nat_e (S O))))))))), a)), Nil))))
                                     | False -> Some (Cons ((Pair ((Pair
                                         (pi0,
                                         (remove_empty_heap pi0
                                           (star_assoc_left 
                                             (star_com sig0) Emp)))), a)),
                                         Nil)))))
                | Lst (e1, e2) -> Some (Cons ((Pair ((Pair (pi0, (Star (Emp,
                    sig0)))), a)), Nil)))
         | WpMutation (e1, e2, l') -> Some (Cons ((Pair ((Pair (pi0, sig0)),
             (WpMutation ((subst_e_lst l e1), (subst_e_lst l e2), (WpSubst
             (l, l')))))), Nil))
         | WpIf (b, l1, l2) -> Some (Cons ((Pair ((Pair (pi0, sig0)), (WpIf
             ((subst_b_lst l b), (WpSubst (l, l1)), (WpSubst (l, l2)))))),
             Nil)))
  | WpLookup (x, e, l) ->
      (match sig0 with
         | Singl (e1, e2) -> Some (Cons ((Pair ((Pair (pi0, (Star (Emp,
             sig0)))), a)), Nil))
         | Cell e1 -> Some (Cons ((Pair ((Pair (pi0, (Star (Emp, sig0)))),
             a)), Nil))
         | Emp -> Some (Cons ((Pair ((Pair (pi0,
             (remove_empty_heap pi0 (star_assoc_left (star_com sig0) Emp)))),
             a)), Nil))
         | Star (s1, s) ->
             (match s with
                | Singl (e1, e2) ->
                    (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e)))) with
                       | True -> Some (Cons ((Pair ((Pair (pi0, sig0)),
                           (WpSubst ((Cons ((Pair (x, e2)), Nil)), l)))),
                           Nil))
                       | False -> Some (Cons ((Pair ((Pair (pi0,
                           (remove_empty_heap pi0
                             (star_assoc_left (star_com sig0) Emp)))), a)),
                           Nil)))
                | Cell e1 ->
                    (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e)))) with
                       | True ->
                           let x' =
                             plus
                               (max (Fresh.var_max_assrt (Pair (pi0, sig0)))
                                 (Fresh.var_max_wpAssrt a)) (S O)
                           in
                           Some (Cons ((Pair ((Pair (pi0, (Star (s1, (Singl
                           (e1, (Var_e x'))))))), (WpSubst ((Cons ((Pair (x,
                           (Var_e x'))), Nil)), l)))), Nil))
                       | False -> Some (Cons ((Pair ((Pair (pi0,
                           (remove_empty_heap pi0
                             (star_assoc_left (star_com sig0) Emp)))), a)),
                           Nil)))
                | Emp -> Some (Cons ((Pair ((Pair (pi0,
                    (remove_empty_heap pi0
                      (star_assoc_left (star_com sig0) Emp)))), a)), Nil))
                | Star (s0, s2) -> Some (Cons ((Pair ((Pair (pi0,
                    (remove_empty_heap pi0
                      (star_assoc_left (star_com sig0) Emp)))), a)), Nil))
                | Lst (e1, e2) ->
                    (match expr_b_dp (Or_b ((Neg_b pi0), (And_b ((Neq_b (e1,
                             e2)), (Eq_b (e1, e)))))) with
                       | True ->
                           let x' = triple_vfresh (Pair (pi0, sig0)) a in
                           Some (Cons ((Pair ((Pair ((And_b ((And_b (pi0,
                           (Neq_b (e1, (Var_e x'))))), (Eq_b ((Var_e x'),
                           (nat_e O))))), (Star ((Star (s1, (Star ((Lst
                           ((Var_e x'), e2)), (Cell (Add_e (e1,
                           (nat_e (S O))))))))), (Singl (e1, (Var_e
                           x'))))))), a)), (Cons ((Pair ((Pair ((And_b
                           ((And_b (pi0, (Neq_b (e1, (Var_e x'))))), (Neq_b
                           ((Var_e x'), (nat_e O))))), (Star ((Star (s1,
                           (Star ((Lst ((Var_e x'), e2)), (Cell (Add_e (e1,
                           (nat_e (S O))))))))), (Singl (e1, (Var_e
                           x'))))))), a)), Nil))))
                       | False ->
                           (match expr_b_dp (Or_b ((Neg_b pi0), (And_b
                                    ((Neq_b (e1, e2)), (Eq_b ((Add_e (e1,
                                    (nat_e (S O)))), e)))))) with
                              | True ->
                                  let x' = triple_vfresh (Pair (pi0, sig0)) a
                                  in
                                  Some (Cons ((Pair ((Pair ((And_b ((And_b
                                  (pi0, (Neq_b (e1, (Var_e x'))))), (Eq_b
                                  ((Var_e x'), (nat_e O))))), (Star ((Star
                                  (s1, (Star ((Lst ((Var_e x'), e2)), (Cell
                                  (Add_e (e1, (nat_e (S O))))))))), (Singl
                                  (e1, (Var_e x'))))))), a)), (Cons ((Pair
                                  ((Pair ((And_b ((And_b (pi0, (Neq_b (e1,
                                  (Var_e x'))))), (Neq_b ((Var_e x'),
                                  (nat_e O))))), (Star ((Star (s1, (Star
                                  ((Lst ((Var_e x'), e2)), (Cell (Add_e (e1,
                                  (nat_e (S O))))))))), (Singl (e1, (Var_e
                                  x'))))))), a)), Nil))))
                              | False -> Some (Cons ((Pair ((Pair (pi0,
                                  (remove_empty_heap pi0
                                    (star_assoc_left (star_com sig0) Emp)))),
                                  a)), Nil)))))
         | Lst (e1, e2) -> Some (Cons ((Pair ((Pair (pi0, (Star (Emp,
             sig0)))), a)), Nil)))
  | WpMutation (e1, e2, l) ->
      (match sig0 with
         | Singl (e3, e4) -> Some (Cons ((Pair ((Pair (pi0, (Star (Emp,
             sig0)))), a)), Nil))
         | Cell e3 -> Some (Cons ((Pair ((Pair (pi0, (Star (Emp, sig0)))),
             a)), Nil))
         | Emp -> Some (Cons ((Pair ((Pair (pi0,
             (remove_empty_heap pi0 (star_assoc_left (star_com sig0) Emp)))),
             a)), Nil))
         | Star (s1, s) ->
             (match s with
                | Singl (e3, e4) ->
                    (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e3)))) with
                       | True -> Some (Cons ((Pair ((Pair (pi0, (Star (s1,
                           (Singl (e3, e2)))))), l)), Nil))
                       | False -> Some (Cons ((Pair ((Pair (pi0,
                           (remove_empty_heap pi0
                             (star_assoc_left (star_com sig0) Emp)))), a)),
                           Nil)))
                | Cell e3 ->
                    (match expr_b_dp (Or_b ((Neg_b pi0), (Eq_b (e1, e3)))) with
                       | True -> Some (Cons ((Pair ((Pair (pi0, (Star (s1,
                           (Singl (e3, e2)))))), l)), Nil))
                       | False -> Some (Cons ((Pair ((Pair (pi0,
                           (remove_empty_heap pi0
                             (star_assoc_left (star_com sig0) Emp)))), a)),
                           Nil)))
                | Emp -> Some (Cons ((Pair ((Pair (pi0,
                    (remove_empty_heap pi0
                      (star_assoc_left (star_com sig0) Emp)))), a)), Nil))
                | Star (s0, s2) -> Some (Cons ((Pair ((Pair (pi0,
                    (remove_empty_heap pi0
                      (star_assoc_left (star_com sig0) Emp)))), a)), Nil))
                | Lst (e3, e4) ->
                    (match expr_b_dp (Or_b ((Neg_b pi0), (And_b ((Eq_b (e1,
                             e3)), (Neq_b (e3, e4)))))) with
                       | True ->
                           let x' = triple_vfresh (Pair (pi0, sig0)) a in
                           Some (Cons ((Pair ((Pair ((And_b ((And_b (pi0,
                           (Neq_b (e3, (Var_e x'))))), (Eq_b ((Var_e x'),
                           (nat_e O))))), (Star ((Star (s1, (Star ((Lst
                           ((Var_e x'), e4)), (Cell (Add_e (e3,
                           (nat_e (S O))))))))), (Singl (e3, (Var_e
                           x'))))))), a)), (Cons ((Pair ((Pair ((And_b
                           ((And_b (pi0, (Neq_b (e3, (Var_e x'))))), (Neq_b
                           ((Var_e x'), (nat_e O))))), (Star ((Star (s1,
                           (Star ((Lst ((Var_e x'), e4)), (Cell (Add_e (e3,
                           (nat_e (S O))))))))), (Singl (e3, (Var_e
                           x'))))))), a)), Nil))))
                       | False ->
                           (match expr_b_dp (Or_b ((Neg_b pi0), (And_b ((Eq_b
                                    ((Add_e (e3, (nat_e (S O)))), e1)),
                                    (Neq_b (e3, e4)))))) with
                              | True ->
                                  let x' = triple_vfresh (Pair (pi0, sig0)) a
                                  in
                                  Some (Cons ((Pair ((Pair ((And_b ((And_b
                                  (pi0, (Neq_b (e3, (Var_e x'))))), (Eq_b
                                  ((Var_e x'), (nat_e O))))), (Star ((Star
                                  (s1, (Star ((Lst ((Var_e x'), e4)), (Singl
                                  (e3, (Var_e x'))))))), (Cell (Add_e (e3,
                                  (nat_e (S O))))))))), a)), (Cons ((Pair
                                  ((Pair ((And_b ((And_b (pi0, (Neq_b (e3,
                                  (Var_e x'))))), (Neq_b ((Var_e x'),
                                  (nat_e O))))), (Star ((Star (s1, (Star
                                  ((Lst ((Var_e x'), e4)), (Singl (e3, (Var_e
                                  x'))))))), (Cell (Add_e (e3,
                                  (nat_e (S O))))))))), a)), Nil))))
                              | False -> Some (Cons ((Pair ((Pair (pi0,
                                  (remove_empty_heap pi0
                                    (star_assoc_left (star_com sig0) Emp)))),
                                  a)), Nil)))))
         | Lst (e3, e4) -> Some (Cons ((Pair ((Pair (pi0, (Star (Emp,
             sig0)))), a)), Nil)))
  | WpIf (b, l1, l2) -> Some (Cons ((Pair ((Pair ((And_b (pi0, b)), sig0)),
      l1)), (Cons ((Pair ((Pair ((And_b (pi0, (Neg_b b))), sig0)), l2)),
      Nil))))

(** val tritra_list : ((pi, sigma) prod, wpAssrt) prod list -> ((pi, sigma)
                      prod, wpAssrt) prod list option **)

let rec tritra_list = function
  | Nil -> Some Nil
  | Cons (p, tl) ->
      let Pair (p0, a) = p in
      let Pair (pi0, sg) = p0 in
      (match match expr_b_dp (Neg_b pi0) with
               | True -> Some Nil
               | False -> tritra_step' pi0 sg a with
         | Some l' ->
             (match tritra_list tl with
                | Some l'' -> Some (app l' l'')
                | None -> None)
         | None -> None)

(** val tritra_list_rec : ((pi, sigma) prod, wpAssrt) prod list -> nat ->
                          ((pi, sigma) prod, wpAssrt) prod list option **)

let rec tritra_list_rec l = function
  | O -> Some l
  | S size' ->
      (match tritra_list l with
         | Some l' ->
             (match l' with
                | Nil -> Some Nil
                | Cons (p, l0) -> tritra_list_rec l' size')
         | None -> None)

(** val wpAssrt_size : wpAssrt -> nat **)

let rec wpAssrt_size = function
  | WpElt p -> S (S O)
  | WpSubst (l, p) -> plus (S (S O)) (wpAssrt_size p)
  | WpLookup (x, e, p) -> plus (S (S O)) (wpAssrt_size p)
  | WpMutation (e1, e2, p) -> plus (S (S O)) (wpAssrt_size p)
  | WpIf (b, l1, l2) ->
      plus (plus (S (S O)) (wpAssrt_size l1)) (wpAssrt_size l2)

(** val triple_transformation_complexity : expr_b -> sigma -> wpAssrt -> nat **)

let triple_transformation_complexity pi0 sig0 l =
  mult (mult (expr_B_size pi0) (sigma_size sig0)) (wpAssrt_size l)

(** val triple_transformation : assrt0 -> wpAssrt -> ((pi, sigma) prod,
                                wpAssrt) prod list option **)

let rec triple_transformation p q =
  match p with
    | Nil -> Some Nil
    | Cons (a, tl) ->
        let Pair (pi0, sig0) = a in
        (match tritra_list_rec (Cons ((Pair ((Pair
                 ((compute_constraints (cell_loc_not_null pi0 sig0) sig0),
                 sig0)), q)), Nil))
                 (triple_transformation_complexity pi0 sig0 q) with
           | Some l ->
               (match triple_transformation tl q with
                  | Some l' -> Some (app l l')
                  | None -> None)
           | None ->
               (match triple_transformation tl q with
                  | Some l' -> Some (Cons ((Pair ((Pair (pi0, sig0)), q)),
                      l'))
                  | None -> None))

type cmd' =
  | Skip'
  | Assign' of Coq_var.v * expr
  | Lookup' of Coq_var.v * expr
  | Mutation' of expr * expr
  | Malloc' of Coq_var.v * expr
  | Free' of expr
  | While' of expr_b * assrt0 * cmd'
  | Seq' of cmd' * cmd'
  | Ifte' of expr_b * cmd' * cmd'

(** val assrt_and_expr_b : assrt0 -> expr_b -> assrt0 **)

let rec assrt_and_expr_b a b =
  match a with
    | Nil -> Nil
    | Cons (a0, tl) ->
        let Pair (pi0, sig0) = a0 in
        Cons ((Pair ((And_b (pi0, b)), sig0)), (assrt_and_expr_b tl b))

(** val vcg : cmd' -> wpAssrt -> (wpAssrt, (assrt0, wpAssrt) prod list) prod
              option **)

let rec vcg c q =
  match c with
    | Skip' -> Some (Pair (q, Nil))
    | Assign' (x, e) -> Some (Pair ((WpSubst ((Cons ((Pair (x, e)), Nil)),
        q)), Nil))
    | Lookup' (x, e) -> Some (Pair ((WpLookup (x, e, q)), Nil))
    | Mutation' (e, f) -> Some (Pair ((WpMutation (e, f, q)), Nil))
    | Malloc' (v0, e) -> None
    | Free' e -> None
    | While' (b, inv, c') ->
        (match vcg c' (WpElt inv) with
           | Some p ->
               let Pair (q', l') = p in
               Some (Pair ((WpElt inv), (Cons ((Pair
               ((assrt_and_expr_b inv (Neg_b b)), q)), (Cons ((Pair
               ((assrt_and_expr_b inv b), q')), l'))))))
           | None -> None)
    | Seq' (c1, c2) ->
        (match vcg c2 q with
           | Some p ->
               let Pair (q2, l2) = p in
               (match vcg c1 q2 with
                  | Some p0 ->
                      let Pair (q1, l1) = p0 in Some (Pair (q1, (app l1 l2)))
                  | None -> None)
           | None -> None)
    | Ifte' (b, c1, c2) ->
        (match vcg c2 q with
           | Some p ->
               let Pair (q2, l2) = p in
               (match vcg c1 q with
                  | Some p0 ->
                      let Pair (q1, l1) = p0 in
                      Some (Pair ((WpIf (b, q1, q2)), (app l1 l2)))
                  | None -> None)
           | None -> None)

(** val triple_transformations : (assrt0, wpAssrt) prod list -> ((pi, sigma)
                                 prod, wpAssrt) prod list option **)

let rec triple_transformations = function
  | Nil -> Some Nil
  | Cons (p, tl) ->
      let Pair (a, l0) = p in
      (match triple_transformation a l0 with
         | Some l1 ->
             (match triple_transformations tl with
                | Some l' -> Some (app l1 l')
                | None -> None)
         | None -> None)

(** val bigtoe_fun : cmd' -> assrt0 -> assrt0 -> ((pi, sigma) prod, wpAssrt)
                     prod list option **)

let bigtoe_fun c p q =
  match vcg c (WpElt q) with
    | Some p0 ->
        let Pair (q', l) = p0 in
        (match triple_transformation p q' with
           | Some l' ->
               (match triple_transformations l with
                  | Some l'' -> Some (app l' l'')
                  | None -> None)
           | None -> None)
    | None -> None


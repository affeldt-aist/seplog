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

open Extracted
open Printf

let printbool b =
    match b with
        | True ->
                printf "True"
        | False ->
                printf "False"

let rec printNat n =
    match n with
        | O -> printf "O"
        | S n' -> printf "S "; printNat n'

let rec printpos p =
    match p with
        | XH -> printf "XH"
        | XI p' -> printf "XI "; printpos p'
        | XO p' -> printf "XO "; printpos p'

let rec printZ n =
    match n with
        | Z0 -> printf "ZO"
        | Zneg p -> printf "- "; printpos p
        | Zpos p -> printf "+ "; printpos p

let rec printexpr e =
    match e with
        | Int_e v -> printZ v
        | Var_e v -> printNat v
        | Add_e (e1,e2) -> printexpr e1; printf " + "; printexpr e2
        | Min_e (e1,e2) -> printexpr e1; printf " - "; printexpr e2
        | Mul_e (e1,e2) -> printexpr e1; printf " * "; printexpr e2
        | _ -> printf "unknown"

let rec printexpr_b b =
    match b with
        | True_b -> printf "TT"
        | Eq_b (e1,e2) -> printexpr e1; printf " == "; printexpr e2
        | Gt_b (e1,e2) -> printexpr e1; printf " > "; printexpr e2
        | Ge_b (e1,e2) -> printexpr e1; printf " >= "; printexpr e2
        | And_b (b1,b2) -> printexpr_b b1; printf " /\\ "; printexpr_b b2
        | Or_b (b1,b2) -> printexpr_b b1; printf " \\/ "; printexpr_b b2
        | Neg_b b1 -> printf "! "; printexpr_b b1
        | _ -> printf "unknown"

let rec printsigma s =
    match s with
        | Epsi -> printf "E"
        | Singl (e1,e2) -> printexpr e1; printf " |-> "; printexpr e2
        | Cell e1 -> printexpr e1; printf " |->_ "; 
        | Star (s1,s2) -> printsigma s1; printf " ** "; printsigma s2

let printfrag f =
    match f with 
        | Pair (b,s) -> printexpr_b b; printf " | "; printsigma s

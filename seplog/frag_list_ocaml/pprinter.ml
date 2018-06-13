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
open Convert

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

let rec reverse_list l =
    match l with
     | Nil -> Nil
     | Cons (e,l') -> app (reverse_list l') (Cons (e,Nil))

let rec printvar' v l =
    match l with
      | Nil -> printf "error"
      | Cons (v',l') ->
             match v with
              | S n' ->  printvar' n' l'
              | O ->  printf "%s" v'


let printvar v l = printvar' v (reverse_list l)


(*
let rec length_int = function
  | Nil -> 0
  | Cons (a, m) -> 1 + (length_int m)


let rec printvar v l =
      printvar' (num2Nat ((nat2num v) - length_int l)) l
*)      

let rec printexpr e l =
    match e with
        | Int_e v -> printf "%d" (z2num v)
        | Var_e v -> printvar v l
        | Add_e (e1,e2) -> printexpr e1 l; printf " + "; printexpr e2 l
        | Min_e (e1,e2) -> printexpr e1 l; printf " - "; printexpr e2 l
        | Mul_e (e1,e2) -> printexpr e1 l; printf " * "; printexpr e2 l
        | _ -> printf "unknown"


let rec printexpr_b b l =
    match b with
        | True_b -> printf "TT"
        | Eq_b (e1,e2) -> printexpr e1 l; printf " == "; printexpr e2 l
        | Neq_b (e1,e2) -> printexpr e1 l; printf " <> "; printexpr e2 l
        | Gt_b (e1,e2) -> printexpr e1 l; printf " > "; printexpr e2 l
        | Ge_b (e1,e2) -> printexpr e1 l; printf " >= "; printexpr e2 l
        | And_b (b1,b2) -> printexpr_b b1 l; printf " /\\ "; printexpr_b b2 l
        | Or_b (b1,b2) -> printexpr_b b1 l; printf " \\/ "; printexpr_b b2 l
        | Neg_b b1 -> printf "! "; printexpr_b b1 l

let rec printsigma s l=
    match s with
        | Emp -> printf "E"
        | Singl (e1,e2) -> printexpr e1 l; printf " |-> "; printexpr e2 l
        | Cell e1 -> printexpr e1 l; printf " |->_ "; 
        | Star (s1,s2) -> printsigma s1 l; printf " ** "; printsigma s2 l
        | Lst (s1,s2) -> printf " list "; printexpr s1 l; printf " "; printexpr s2 l

let printfrag f l=
    match f with 
        | Pair (b,s) -> printexpr_b b l; printf " | "; printsigma s l


let rec printAssrt a l=
    match a with 
        | Nil -> printf ""
        | Cons (f,a') -> printf "{"; printfrag f l; printf "}"; printAssrt a' l

let rec printindent i =
     match i with
         | 0 -> printf ""
         | _ -> printf "\t"; printindent (i - 1)

let rec printcmd c i l =
    match c with
       | Skip' -> printindent i; printf "Skip"
       | Assign' (v,e) -> printindent i; printvar v l; printf " <- "; printexpr e l
       | Lookup' (v,e) -> printindent i; printvar v l; printf " <-* "; printexpr e l
       | Mutation' (e1,e2) -> printindent i; printexpr e1 l; printf " *<- "; printexpr e2 l
       | Malloc' (x,e) -> printindent i; printf "malloc ("; (printvar x l); printf ","; printexpr e l; printf ")"
       | Free' e -> printindent i;  printf "free ("; printexpr e l; printf ")"
       | While' (b,a,c') -> printindent i; printf "while ("; printexpr_b b l; printf ")\n"; printindent (i+1); printf "["; printAssrt a l; printf "]{\n"; printcmd c' (i+1) l; printf "\n"; printindent (i); printf "}"
       | Seq' (c1,c2) -> printcmd c1 i l; printf ";\n"; printcmd c2 i l
       | Ifte' (b,c1,c2) -> printindent i; printf "if ("; printexpr_b b l; printf "){\n"; printcmd c1 (i+1) l; printf "\n"; printindent i; printf "} else {\n"; printcmd c2 (i+1) l; printf "\n"; printindent i; printf "}"

let rec printassign l i a =
    match l with
       | Nil -> printf ""
       | Cons ((Pair (v,e)), l') -> printindent i; printvar v a; printf " <- "; printexpr e a; printassign l' i a


let rec printlassrt l i s =
    match l with
       | WpElt a -> printf "\n"; printAssrt a s
       | WpSubst (l',l'') -> printf "\n"; printassign l' i s; printf ";"; printlassrt l'' i s
       | WpLookup (v,e,l') -> printf "\n"; printindent i; printvar v s; printf " <-* "; printexpr e s; printf ";"; printlassrt l' i s
       | WpMutation (e1,e2,l') -> printf "\n"; printindent i; printexpr e1 s; printf " *<- "; printexpr e2 s; printf ";"; printlassrt l' i s
       | WpIf (b,l1,l2) -> printindent i;
                           printf "if ("; 
                           printexpr_b b s; 
                           printf "){"; 
                           printlassrt l1 (i+1) s; 
                           printf "\n"; 
                           printindent i; 
                           printf "} else {"; 
                           printlassrt l2 (i+1) s; 
                           printf "\n"; 
                           printindent i; 
                           printf "}"

let rec printce l i s =
    match l with
      | Nil -> printf ""
      | Cons (Pair (a, l1 ),l2) ->
           printf "Goal %d:\n" i;
           printf "{"; printfrag a s; printf "}"; printlassrt l1 0 s; printf "\n\n"; printce l2 (i+1) s

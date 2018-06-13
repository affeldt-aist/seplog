/*
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
 */


%{
open Printf
open Lexing
open Extracted
open Pprinter
open Convert


let rec length_int = function
  | Nil -> 0
  | Cons (a, m) -> 1 + (length_int m)

let rec varindex v l = 
  match l with 
  | Nil -> 1
  | Cons (a, m) -> 
        if (String.compare v a == 0) then 0 else (1 + varindex v m)

type vlist = {mutable l: string list};;

let varlist : vlist =  {l = Nil} ;;            
        
let var2Nat v lst = 
        if (varindex v lst.l > length_int lst.l) then (
               (lst.l <- Cons (v, lst.l)); 
               num2Nat (length_int lst.l - 1)
        ) else (
               num2Nat ((length_int lst.l) - (varindex v lst.l) - 1)
        )



%}

/*  */
%token NEWLINE EOF

/* The numbers */
%token <int> NUM

/* The indentifiers */
%token <string> VAR

/* The integer oprators */
%token PLUS MINUS MULT FIELD

/* The comparaison operators */
%token GT LT GE LE EQ

/* The boolean operator */
%token NEG AND OR IMPL

/* The true value */
%token TRUE

/* The separation */
%token SEPCON EPSILON MAPSTO CELL

/* parenthese */
%token LPAREN RPAREN
%token LACCOL RACCOL

/* implication */
%token TURNSTIL

/* between pure/spatial expression */
%token FRONT

/* command */
%token SKIP ASSIGN LOOKUP MUTATION SEQ IF THEN ELSE WHILE DO

%start input
%type <unit> input

%% /* Grammar rules and actions follow */


input:          presburger EOF { $1 }
                | entail EOF { $1 }
                | hoare EOF { $1 }
;               

expr_num:       NUM {Int_e (num2Z $1) }
                | VAR { Var_e (var2Nat $1 varlist) }          
                | expr_num PLUS expr_num { Add_e ($1, $3) }
                | expr_num FIELD expr_num { Add_e ($1, $3) }
                | expr_num MINUS expr_num { Min_e ($1, $3) }
                | expr_num MULT expr_num { Mul_e ($1, $3) }
                | LPAREN expr_num RPAREN { $2 }
;       

expr_bool:      TRUE { True_b }
                | expr_num GT expr_num  { Gt_b ($1,$3) }
                | expr_num GE expr_num  { Ge_b ($1,$3) }
                | expr_num LE expr_num  { Neg_b (Gt_b ($1,$3)) }
                | expr_num LT expr_num  { Neg_b (Ge_b ($1,$3)) }
                | expr_num EQ expr_num  { (Eq_b ($1,$3)) }
                | NEG expr_bool  {(Neg_b ($2)) }
                | expr_bool AND expr_bool { (And_b ($1,$3)) }
                | expr_bool OR expr_bool { (Or_b ($1,$3))}
                | expr_bool IMPL expr_bool { (Or_b (Neg_b $1,$3)) }
                | LPAREN expr_bool RPAREN { $2 }
;

presburger:     expr_bool   {printf "Presburger(\n";
                             printexpr_b $1;
                             printf "\n):";
                             printbool (presburgerB $1);
                             printf "\n";
                            }
;


sigma:          EPSILON { Epsi }
                | expr_num MAPSTO expr_num { Singl ($1,$3)}
                | sigma SEPCON sigma { Star ($1,$3) }
                | expr_num CELL { Cell $1 }
                | LPAREN sigma RPAREN { $2 }
;

expr_frag:      expr_bool FRONT sigma { Pair ($1,$3) }
                | LPAREN expr_frag RPAREN { $2 }
;

entail:         expr_frag TURNSTIL expr_frag  {  printf "entail(\n";
                                                 printfrag $1;
                                                 printf " |- ";
                                                 printfrag $3;
                                                 printf "\n):";
                                                 printbool (frag_decision $1 $3);
                                                 printf "\n";
                                                }
;

cmd:            VAR ASSIGN expr_num { Assign ((var2Nat $1 varlist),$3) }
                | VAR LOOKUP expr_num { Lookup ((var2Nat $1 varlist),$3) }
                | expr_num MUTATION expr_num { Mutation ($1,$3) }
                | cmd SEQ cmd { Seq ($1,$3) }
                | IF expr_bool THEN cmd ELSE cmd {Ifte ($2,$4,$6)}
;

cond:           LACCOL expr_frag RACCOL { $2 }
;

hoare:          cond cmd cond {printbool (printf "hoare:"; frag_hoare $1 $3 $2); printf "\n";}
;
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

{
  open Grammar 

}

let digit = ['0'-'9']
let ident = ['a'-'z' 'A'-'Z']
let ident_num = ['a'-'z' 'A'-'Z' '0'-'9']
rule token = parse
  | [' ' '\t' '\n' '\r']+ { token lexbuf }

  | "|-"        { TURNSTIL }                

  | 'E'         { EPSILON }              
  | "**"        { SEPCON }
  | "|->_"      { CELL }
  | "|->"       { MAPSTO }
  | "list"       { LIST }


  | '|'         { FRONT } 

  | "skip"      { SKIP }
  | "*<-"       { MUTATION }     
  | "<-*"       { LOOKUP }
  | "<-"        { ASSIGN }
  | ":="        { ASSIGN2 }
  | ';'         { SEQ }
  | "if"        { IF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | "while"     { WHILE }       
  | "do"        { DO }
          
  | "TT"        { TRUE }
  | "=="        { EQ }
  | "<>"        { NEQ }
  | '<'		{ LT }
  | "<="	{ LE }
  | '>'		{ GT }
  | ">="	{ GE }
  | '!'         { NEG }      

  | "/\\"        { AND }
  | "\\/"        { OR }
  | "->"        { IMPL }

  | '+'		{ PLUS }
  | '-'		{ MINUS }
  | '*'		{ MULT }
  | "-.>"        { FIELD }        

  | digit+ as num
                { NUM (int_of_string num) }
  | ident ident_num* as word { VAR word }

  | ','         { COMMA }       

  | '('		{ LPAREN }
  | ')'		{ RPAREN }

  | '{'		{ LACCOL }
  | '}'		{ RACCOL }

  | '['		{ LBRACK }
  | ']'		{ RBRACK }

  | eof		{ EOF }

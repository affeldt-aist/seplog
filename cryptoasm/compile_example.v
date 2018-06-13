(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import ZArith_ext.
Require Import machine_int.
Import MachineInt.

Require Import multi_int.
Require Import mips_seplog.
Require Import compile.

Local Open Scope multi_int_scope.

Module compile_m := Compile WMIPS_Hoare.

Require Import mont_mul_prg mont_mul_triple.

Definition k := reg_s6.
Definition alpha := reg_s7.
Definition x := reg_a0.
Definition y := reg_a1.
Definition z := reg_a2.
Definition m := reg_a3.

Definition one := reg_t0.
Definition ext := reg_t1.
Definition int_ := reg_t2.
Definition X_ := reg_t3.
Definition Y_ := reg_t4.
Definition M_ := reg_t5.
Definition Z_ := reg_t6.
Definition quot := reg_t7.
Definition C := reg_t8.

Definition t := reg_v0.
Definition s_ := reg_v1.

Lemma Hset : uniq (k :: alpha :: x :: y :: z :: m :: one :: ext :: int_ :: X_ ::
  Y_ :: M_ :: Z_ :: quot :: C :: t :: s_ :: r0 :: nil). Proof. done. Qed.

Section test.

Variable nk : nat.
Variables X Y M : seq (int 32).
Hypothesis Hx : length X = nk.
Hypothesis Hy : length Y = nk.
Hypothesis Hm : length M = nk.
Hypothesis HX : \S_{ nk } X < \S_{ nk } M.
Hypothesis HY : \S_{ nk } Y < \S_{ nk } M.
Variables vx vy vm vz : int 32.
Hypothesis Hnz : u2Z vz + 4 * Z_of_nat nk < Zbeta 1.
Variable valpha : int 32.

Local Open Scope eqmod_scope.
Local Open Scope machine_int_scope.

Hypothesis Halpha : u2Z (M `32_ 0) * u2Z valpha =m -1 {{ Zbeta 1 }}.

(** * Application: Generation of Hoare-logic Proofs from %\while%#While#

   %\label{sec:application}%

   *)

(**
   %\label{sec:montgomery}%

   %As explained in Section \ref{sec:intro}, % in %\cite{affeldt06asian}%#[Affeldt&Marti2006]#,
   we verified in Coq an implementation of the Montgomery multiplication written in the SmartMIPS instruction set.
   We worked on a version of the program where branches were replaced by while-loops and
   while-loops where compiled away by a certified macro-expander afterwards. Strictly speaking, there was
   therefore no Hoare-logic proof for the assembly code to be run.

   The rest of this section shows that one can recover a Hoare-logic proof for the assembly code to be run
   by using the previously formalized theorem %\coqdocvar{preservation\_hoare}%#preservation_hoare#
   %(Section \ref{thm:hoare-triple-preservation})%.

*)

(** %\coqdocvar{montgomery}%#montgomery# is the program with while-loops. We instantiate it with
   a set of registers: *)

Definition mont_mul_cmd : while.cmd := montgomery k alpha x y z m one ext int_ X_ Y_ M_ Z_ quot C t s_.

(** Given a certain set of parameters (concrete initial values to put in registers and in the mutable memory),
   the proof of correctness %\coqdocvar{mont\_mul\_specif}%#mont_mul_triple# gives a proof-term that is the
   proof that the Montgomery multiplication with while-loops is correct. In other words, this is a proof of
   correctness prior to compilation. This is clear when checked with the %\texttt{Check}%#Check# command.*)

Definition mont_mul_cmd_hoare :=
  mont_mul_triple _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hset nk valpha vx vy vm vz X Y M Halpha Hx Hy Hm Hnz HX HY.

Local Open Scope mips_expr_scope.
Import assert_m.
Local Open Scope mips_assert_scope.
Local Open Scope mips_cmd_scope.
Local Open Scope mips_hoare_scope.

Check mont_mul_cmd_hoare.

(**
%\small\begin{verbatim}
> Check mont_mul_cmd_hoare.
{{fun s h => [x]_s = vx /\ [y]_s = vy /\ [z]_s = vz /\ [m]_s = vm /\
  u2Z ([k]_s) = Z_of_nat nk /\ [alpha]_s = valpha /\
  (((var_e x |--> X ** var_e y |--> Y) ** var_e z |--> nseq nk zero32) **
   var_e m |--> M) s h /\
  store.multi_null s}}
montgomery k alpha x y z m one ext int_ X_ Y_ M_ Z_ quot C t s_
{{fun s h => exists Z0, length Z0 = nk /\
  [x]_s = vx /\ [y]_s = vy /\ [z]_s = vz /\ [m]_s = vm /\
  u2Z ([k]_s) = Z_of_nat nk /\ [alpha]_s = valpha /\
  (((var_e x |--> X ** var_e y |--> Y) ** var_e z |--> Z0) ** var_e m |--> M) s h /\
  (Zbeta nk * \S_{ nk }.+1 (Z0 ++ [C]_s :: nil) =m \S_{ nk } X * \S_{ nk } Y {{\S_{ nk } M}}) /\
  \S_{ nk }.+1 (Z0 ++ [C]_s :: nil) < 2 * \S_{ nk } M /\
  u2Z ([t]_s) = 4 * nz + 4 * Z_of_nat (nk - 1)}}
\end{verbatim}\normalsize%

Now, let us consider %\coqdocvar{mont\_mul\_scode}%#mont_mul_scode#, the Montgomery multiplication with gotos,
obtained by automatically macro-expanding if-then-else's and while-loops and locating the code at
starting label 0
   (using a function corresponding to the %\coqdocvar{compile}%#compile#
   predicate %(see Section \ref{sec:compile})%): *)

Definition mont_mul_scode : compile_m.sgoto_hoare_m.sgoto_m.scode := compile_m.compile_f O mont_mul_cmd.

Set Printing Depth 100.
Eval vm_compute in (compile_m.compile_f O mont_mul_cmd).

Lemma Hcompile : compile_m.compile O mont_mul_cmd mont_mul_scode 38%nat.
Proof.
have <- : (O + size (compile_m.sgoto_hoare_m.sgoto_m.sdom mont_mul_scode) = 38)%nat by vm_compute.
apply compile_m.compile_f_compile.
rewrite /mont_mul_scode.
reflexivity.
Qed.

(** By application of %\coqdocvar{preservation\_hoare}%#preservation_hoare# and given the proof that the
   Montgomery multiplication with while-loops is correct, we obtain a proof-term that is the proof
   that the Montgomery multiplication %{\em% with gotos%}% is correct. Again,
   this can be checked with the %\texttt{Check}%#Check# command:
   the same triple as above is shown to hold, with the additional information that the starting label is 0, and the ending label is 38. *)

Definition mont_mul_sgoto_hoare :=
  compile_m.preservation_hoare _ _ _ mont_mul_cmd_hoare _ _ _ Hcompile.

(**
%\small\begin{verbatim}
> Check mont_mul_sgoto_hoare.
compile_m.sgoto_hoare_m.hoare_sgoto
(fun pc s h0 => pc = /\ (fun s0 h =>
 [x]_s0 = vx /\ [y]_s0 = vy /\ [z]_s0 = vz /\ [m]_s0 = vm /\
 u2Z ([k]_s0) = Z_of_nat nk /\ [alpha]_s0 = valpha /\
 (((var_e x |--> X ** var_e y |--> Y) ** var_e z |--> nseq nk zero32) **
  var_e m |--> M) s0 h /\
 store.multi_null s0) s h0)
mont_mul_scode
(fun pc s h0 => pc = 38 /\ (fun s0 h => exists Z0, length Z0 = nk /\
 [x]_s0 = vx /\ [y]_s0 = vy /\ [z]_s0 = vz /\ [m]_s0 = vm /\
 u2Z ([k]_s0) = Z_of_nat nk /\ [alpha]_s0 = valpha /\
 (((var_e x |--> X ** var_e y |--> Y) ** var_e z |--> Z0) ** var_e m |--> M) s0 h /\
 (Zbeta nk * \S_{ nk }.+1 (Z0 ++ [C]_s0 :: nil) =m \S_{ nk } X * \S_{ nk } Y {{\S_{ nk } M}}) /\
 \S_{ nk }.+1 (Z0 ++ [C]_s0 :: nil) < 2 * \S_{ nk } M /\
 u2Z ([t]_s0) = 4 * nz + 4 * Z_of_nat (nk - 1)) s h0)
\end{verbatim}\normalsize%
*)

End test.
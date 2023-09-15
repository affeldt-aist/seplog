(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
Require Import ssrZ ZArith_ext machine_int.
Import MachineInt.
Require Import mips_cmd.

Local Open Scope mips_cmd_scope.
Import expr_m.

(** The Montgomery multiplication %\cite{montgomery}% is a modular
multiplication.  The advantage of the Montgomery multiplication is
that it does not require multi-precision division, but used
less-expensive shifts instead.  The price to pay is a parasite
multiplicative factor whose elimination requires two passes.

The implementation of the Montgomery multiplication we deal with is
the so-called ``Finely Integrated Operand Scanning'' (FIOS) variant
%\cite{koc1996}%. Intuitively, it resembles the classical algorithm
for multi-precision multiplication: it has two nested loops, the
inner-loop incrementally computes partial products (modulo) that are
successively added by the outer-loop. These partial products are
computed in such a way that the least significant word is always zero,
thus guaranteeing that the final result will fit in $k+1$#k+1# words
of storage (where $k$#k# is the length of multi-precision
integers). For this to be possible, the Montgomery multiplication
requires the pre-computation of the modular inverse of the least
significant work of the modulus.

The SmartMIPS architecture is well-suited to the implementation of the FIOS variant of
the Montgomery multiplication because the addition performed in the inner-loop
(that adds two products of 32-bits integers) fits in the integer multiplier
(of size greater than 72 bits).
*)
Definition montgomery
  k alpha (* saved temporaries *)
  x y z m (* function arguments *)
  one ext int X Y M Z quot C (* temporaries *)
  t s (* return values *) :=
  addiu one r0 one16 ;
  addiu C r0 zero16 ;
  addiu ext r0 zero16 ;
  While (bne ext k) {{
    lwxs X ext x ;
    lw Y zero16 y ;
    lw Z zero16 z ;
    multu X Y ;
    lw M zero16 m ;
    maddu Z one ;
    mflo t ;
    mfhi s ;
    multu t alpha ;
    addiu int r0 one16 ;
    mflo quot ;
    mthi s ;
    mtlo t ;
    maddu quot M ;
    mflhxu Z ;
    addiu t z zero16 ;
    While (bne int k) {{
      lwxs Y int y ;
      lwxs Z int z ;
      maddu X Y ;
      lwxs M int m ;
      maddu Z one ;
      maddu quot M ;
      addiu int int one16 ;
      mflhxu Z ;
      addiu t t four16 ;
      sw Z mfour16 t }} ; (* NB: appear syntactically after the branch in the original code *)
    maddu C one ;
    mflhxu Z ;
    addiu ext ext one16 ;
    sw Z zero16 t ;
    mflhxu C }}. (* NB: appear syntactically after the branch in the original code *)    


Local Open Scope machine_int_scope.
Local Open Scope eqmod_scope.
Local Open Scope zarith_ext_scope.

(** Let %\coqdocvar{A}%#A# by the value of the multiplier before
entering the inner-loop and $\coqdocvar{A}\%\coqdocvar{n}$ #A % n# be the
remainder of the division of %\coqdocvar{A}%#A# by $2^n$#2^n#. The
Montgomery multiplication computes $ quot = ((A \% 32) \odot alpha) \% 32 $
#quot = ((A%32) `* alpha)%32# and adds $quot \odot M0$ #quot `* M0#
to the multiplier. The lemma below captures the fact that the
resulting multiplier is a multiple of $2^{32}$#2^32#, and thus the
least significant word of the partial product is always zero: *)
Lemma montgomery_lemma : forall alpha vm, u2Z vm * u2Z alpha =m -1 {{ \B^1 }} ->
  forall (A : int 64) (m : store.t) ,
    store.utoZ m < \B^2 -> store.utoZ m = u2Z A ->
    store.lo (store.maddu_op ((((A `% 32) `* alpha) `% 32) `* vm) m) = zero32.
Proof.
move=> alpha0 m0 H A mu H0 H1.
apply lo_remainder_zero.
rewrite store.utoZ_maddu.
- rewrite H1.
  inversion_clear H as [K H2].
  exists ((K * (u2Z A)) - (K * \B^1 * (u2Z (shr_shrink 32 A))) +
    (u2Z (shr_shrink 32 A)) -
    ((u2Z m0) * (u2Z (shr_shrink 32 (umul (rem 32 A) alpha0))))).
  rewrite (@u2Z_umul 32) u2Z_rem //; last repeat constructor.
  rewrite (@u2Z_umul 32) u2Z_rem //; last repeat constructor.
  rewrite -Zbeta1E 4!mulZBl mulZDl mulZBl -mulZA -(mulZC (u2Z m0)) H2.
  rewrite (_ : u2Z (shr_shrink 32 A) * \B^1 * u2Z alpha0 * u2Z m0 =
    u2Z (shr_shrink 32 A) * \B^1 * (u2Z m0 * u2Z alpha0)); last ring.
  rewrite H2; ring.
- have H2 : 1 <= 2 ^^ store.acx_size - 1.
    have H2 : 2 ^^ 8 <= 2 ^^ store.acx_size.
      by apply/leZP; rewrite Zpower_2_le store.acx_size_min.
    exact: (@leZ_trans (2 ^^ 8 - 1)).
  exact: (@ltZ_leZ_trans \B^2).
Qed.

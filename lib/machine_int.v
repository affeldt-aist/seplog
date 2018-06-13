(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ProofIrrelevance.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrZ ZArith_ext Init_ext ssrnat_ext seq_ext.
Require Import listbit listbit_correct order.

(***************************************************************************)
(* This file provides:                                                     *)
(* - a module type for the type "int : nat -> Type" of integers of         *)
(*   finite-length (the parameter is the length in bits of the underlying  *)
(*   bitstring);this typecan be regarded as an signed (resp. unsigned)     *)
(*   integer using function s2Z (resp. u2Z); this type is accompanied with *)
(*   various functions and their arithmetic properties                     *)
(* - an implementation using lists of bits                                 *)
(* - Further properties derivable outside the module                       *)
(* - Definitions of often-used finite size integers                        *)
(***************************************************************************)

Reserved Notation "'`(' x ')_' n" (at level 9, format "'`('  x  ')_' n").
Reserved Notation "'`(' x ')c_' n" (at level 9, format "'`('  x  ')c_' n").
Reserved Notation "'`(' x ')s_' n" (at level 9, format "'`('  x  ')s_' n").
Reserved Notation "'`(' x ')sc_' n" (at level 9, format "'`('  x  ')sc_' n").
Reserved Notation "a '`<' b" (at level 75, format "'[' a  `<  b ']'").
Reserved Notation "a '`<=' b" (at level 75, format "'[' a  `<=  b ']'").
Reserved Notation "a '`+' b" (at level 35, format "'[' a  `+  b ']'").
Reserved Notation "a '`-' b" (at level 35, format "'[' a  `-  b ']'").
Reserved Notation "a '`*' b" (at level 50, format "'[' a  `*  b ']'").
Reserved Notation "a '`%' n" (at level 50, format "'[' a  `%  n ']'").
Reserved Notation "a '`<<' n" (at level 50, format "'[' a  `<<  n ']'").
Reserved Notation "a '`>>' n" (at level 50, format "'[' a  `>>  n ']'").
Reserved Notation "a '`&' b" (at level 50).
Reserved Notation "a '`|`' b" (at level 50, format "'[' a  `|`  b ']'").
Reserved Notation "a '`(+)' b" (at level 50).
Reserved Notation "a '`||' b " (at level 68, left associativity, format "'[' a  `||  b ']'").

Set Implicit Arguments.
Unset Strict Implicit.

Local Close Scope N_scope.
Local Open Scope zarith_ext_scope.

(** definition of machine integers as a list of bits of a known length *)
Inductive int n : Type := mk_int (lst : list bool) of size lst = n.

Module Type MACHINE_INT.

Parameter make_int : forall (n : nat) (lst : list bool), size lst = n -> int n.
Parameter dec_int : forall n (a b : int n), {a = b} + {a <> b}.

Parameter cast : forall {f : nat -> nat -> nat} {P}
  (_ : forall k n, P k n -> f k n = n) {k n} (_ : P k n),
  int (f k n) -> int n.
Definition cast_subnK {k n : nat} (H : (k <= n)%nat) := cast subnK H.
Definition cast_subnKC {k n : nat} (H : (k <= n)%nat) := cast subnKC H.
Parameter castC : forall {n m : nat} (H : n = m), int n -> int m.
Parameter castA : forall {n m k} (H : (n + (m + k) = n + m + k)%nat),
  int (n + (m + k)) -> int (n + m + k).

Parameter u2Z : forall n, int n -> Z.
Parameter u2Zc : forall n, int n -> Z.
Parameter u2ZE : forall n (a : int n), u2Z a = u2Zc a.
Parameter max_u2Z : forall n (a : int n), u2Z a < 2 ^^ n.
Parameter min_u2Z : forall n (a : int n), 0 <= u2Z a.
Arguments min_u2Z [n] _ _.
Parameter u2Z_inj : forall n (v w : int n), u2Z v = u2Z w -> v = w.
Parameter u2Z_cast : forall (f : nat -> nat -> nat) (P : nat -> nat -> Type)
  (H : forall k n : nat, P k n -> f k n = n) k n (Hkn : P k n) a,
  u2Z (cast H Hkn a) = u2Z a.
Parameter u2Z_eq_rect : forall n (a : int n) m (H : n = m),
  u2Z (eq_rect _ _ a _ H) = u2Z a.
Parameter u2Z_castC :
  forall m n (a : int n) (H : n = m), u2Z (castC H a) = u2Z a.
Parameter u2Z_castA : forall n m k (a : int _) (H : (n + (m + k) = n + m + k)%nat),
  u2Z (castA H a) = u2Z a.

Parameter bits : forall (n : nat), int n -> list bool.
Parameter size_bits : forall n (a : int n), size (bits a) = n.
Parameter bits2u : forall n : nat, list bool -> int n.
Parameter u2Z_bits2u_u2Z : forall n l, size l = n -> u2Z (bits2u n l) = bitZ.u2Z l.

(** Z2u n z builds an unsigned machine integer of decimal value z and length n (if possible) *)
Parameter Z2u : forall n (z : Z), int n.
Parameter Z2uc : forall n (z : Z), int n.
Notation "'`(' x ')_' n" := (Z2u n x) : machine_int_scope.
Notation "'`(' x ')c_' n" := (Z2uc n x) : machine_int_scope.
Local Open Scope machine_int_scope.
Parameter Z2uE : forall n (z : Z), `( z )_ n = `( z )c_ n.
Parameter Z2uK : forall z n, 0 <= z < 2 ^^ n -> u2Z (Z2u n z) = z.
Parameter u2Z_Z2u_Zmod : forall z n, 0 <= z -> u2Z (Z2u n z) = z mod (2 ^^ n).
Parameter u2Z_Z2u_neg : forall z n, z < 0 -> u2Z (Z2u n z) = 0.
Parameter Z2u_u2Z : forall n (a : int n), Z2u n (u2Z a) = a.
Parameter Z2u_dis : forall n a b, 0 <= a < 2 ^^ n -> 0 <= b < 2 ^^ n ->
  a <> b -> Z2u n a <> Z2u n b.
Parameter bits_zeros : forall n, bits (Z2u n 0) = bits.zeros n.
Parameter Z2u_inj : forall n a b, (0 <= a < 2 ^^ n)%Z -> (0 <= b < 2 ^^ n)%Z ->
  Z2u n a = Z2u n b -> a = b.

(** zero extend *)
Parameter zext : forall m n, int n -> int (m + n).
Parameter zext_zext : forall n (a : int n) m k, castA (@addnA _ _ _) (zext k (zext m a)) = (zext (k + m) a).
Parameter zext_Z2u : forall n m m', n < 2 ^^ m -> zext m' (Z2u m.+1 n) = Z2u (m' + m.+1) n.
Parameter u2Z_zext : forall k n (a : int n), u2Z (zext k a) = u2Z a.

(** sign extend *)
Parameter sext : forall m n (a : int n), int (n + m).
Parameter u2Z_sext : forall n (v : int n) k, 0 <= u2Z v < 2 ^^ n.-1 ->
  u2Z (sext k v) = u2Z v.
Parameter sext_Z2u: forall n m m', n < 2 ^^ m -> sext m' (Z2u m.+1 n) = Z2u (m.+1 + m') n.

Parameter lt_n : forall n, int n -> int n -> bool.
Notation "a '`<' b" := (lt_n a b) : machine_int_scope.
Local Open Scope machine_int_scope.

Parameter le_n : forall n, int n -> int n -> bool.
Notation "a '`<=' b" := (le_n a b) : machine_int_scope.
Parameter le_n_refl : forall n (a : int n), a `<= a.
Parameter le_nE : forall n (a b : int n), a `<= b -> a = b \/ a `< b.

(** arithmetic/logical operations and their properties *)

Parameter add : forall n, int n -> int n -> int n.
Notation "a '`+' b" := (add a b) : machine_int_scope.
Parameter addC : forall n (a b : int n), a `+ b = b `+ a.
Parameter addA : forall n (a b c : int n), (a `+ b) `+ c = a `+ (b `+ c).
Parameter addi0 : forall n (a : int n), a `+ Z2u n 0 = a.

Parameter sub : forall n, int n -> int n -> int n.
Notation "a '`-' b" := (sub a b) : machine_int_scope.

(** unsigned multiplication with truncation *)
Parameter mul : forall n, int n -> int n -> int n.

Parameter umul : forall n (a b : int n), int (n + n).
Notation "a '`*' b" := (umul a b) : machine_int_scope.
Parameter umulC : forall n (a b : int n), a `* b = b `* a.
Parameter umul_1 : forall n (x : int n), x `* Z2u n 1 = zext n x.
Parameter umul_0 : forall n (x : int n), x `* Z2u n 0 = Z2u (n + n) 0.

Parameter smul : forall n, int n -> int n -> int (2 * n).

(** returns the m last bits of (int n) *)
Parameter rem : forall m n, int n -> int m.
Notation "a '`%' n" := (rem n a) : machine_int_scope.
Parameter rem_Zpower : forall n k, (k < n)%nat -> Z2u n (2 ^^ k) `% k = Z2u k 0.

(** left shift *)
Parameter shl : forall (m : nat) n (a : int n), int n.
Notation "a '`<<' n" := (shl n a) : machine_int_scope.
Parameter shl_zero : forall n m,  Z2u n 0 `<< m = Z2u n 0.
Parameter shl_1 : forall n k, (k <= n)%nat -> Z2u n 1 `<< k = Z2u n (2 ^^ k).
Parameter bits_shl_1 : forall n m, (m < n)%nat -> bits (Z2u n 1 `<< m) = bits.zeros m ++ true::nil ++ bits.zeros (n - m - 1).
Parameter shl_rem_m : forall n (a : int n) m, (m <= n)%nat -> (a `<< m) `% m = Z2u m 0.

Parameter shl_ext : forall m n (a : int n), int (m + n).

(** logical right shift *)
Parameter shrl : nat -> forall n, int n -> int n.
Notation "a '`>>' n" := (shrl n a) : machine_int_scope.
Parameter shrl_comp : forall m k n (a : int n), (a `>> k) `>> m = a `>> (k + m).
Parameter shrl_0 : forall n (a : int n), a `>> 0 = a.
Parameter shrl_Z2u_0 : forall n k, Z2u n 0 `>> k = Z2u n 0.
Parameter shrl_Zpower : forall n k l, (k < n)%nat -> (l <= k)%nat -> Z2u n (2 ^^ k) `>> l = Z2u n (2 ^^ (k - l)).

Parameter shrl_overflow : forall n (a : int n) k, u2Z a < 2 ^^ k -> a `>> k = Z2u n 0.
Parameter shl_shrl : forall n (a : int n) m, u2Z a < 2 ^^ m -> (a `<< (n - m)) `>> (n - m) = a.
Parameter shrl_shl : forall n (a : int n) m, a `% m = Z2u m 0 -> (a `>> m) `<< m = a.
Parameter shrl_rem : forall n (a : int n) k k' (kk' : (n = k + k')%nat),
  (zext k ((a `>> k )`% k')) = @eq_rect _ _ _ (a `>> k) _ kk'.

(** arithmetic right shift *)
Parameter shra : nat -> forall n, int n -> int n.
Parameter shr_shrink : forall m n (a : int n), int (n - m)%nat.
Parameter shr_shrink_overflow : forall n (a : int n) k, (k >= n)%nat -> shr_shrink k a = Z2u (n - k)%nat 0.

Parameter int_and : forall n, int n -> int n -> int n.
Notation "a '`&' b" := (int_and a b) : machine_int_scope.
(** x & 0 = 0 *)
Parameter int_and_0 : forall n a, a `& Z2u n 0 = Z2u n 0.
Parameter int_andC : forall n (a b : int n), a `& b = b `& a.
(** x & x = x *)
Parameter int_and_idempotent : forall n (a : int n), a `& a = a.
Parameter int_even_and_1 : forall n (a : int n), Zeven (u2Z a) -> a `& Z2u n 1 = Z2u n 0.
Parameter int_odd_and_1 : forall n (a : int n), Zodd (u2Z a) -> a `& Z2u n 1 = Z2u n 1.
Parameter int_and_rem_1 : forall n (a : int n), u2Z (a `& Z2u n 1) = u2Z (a `% 1).
(** x mod 2^n = x & (2^n - 1)*)
Parameter rem_and : forall n (a : int n) k (Hkn : (k <= n)%nat),
  cast_subnK Hkn (zext (n - k)%nat (a `% k)) = a `& Z2u n (2 ^^ k - 1).

Parameter int_or : forall n, int n -> int n -> int n.
Notation "a '`|`' b" := (int_or a b) : machine_int_scope.
(** x | 0 = x *)
Parameter int_or_0 : forall n (a : int n), a `|` Z2u n 0 = a.
Parameter int_orC : forall n (a b : int n), a `|` b = b `|` a.
(** x | x = x*)
Parameter int_or_idempotent : forall n (a : int n), a `|` a = a.
Parameter bits_int_or : forall n (a b : int n), bits (a `|` b) = bits.or (bits a) (bits b).
Parameter shl_distr_or : forall n (a b : int n) m, (a `|` b) `<< m = (a `<< m) `|` (b `<< m).
Parameter shrl_distr_or : forall n (a b : int n) m, (a `|` b) `>> m = (a `>> m) `|` (b `>> m).
Parameter rem_distr_or : forall n (a b : int n) m, (a `|` b) `% m = (a `% m) `|` (b `% m).
Parameter or_sh_rem : forall n (a : int n) k (H : (k <= n)%nat),
  a = ((a `>> k) `<< k) `|` (cast_subnK H (zext (n - k) (a `% k))).

Parameter int_xor : forall n, int n -> int n -> int n.
Notation "a '`(+)' b" := (int_xor a b) : machine_int_scope.
(** x (+) 0 = x *)
Parameter int_xor_0 : forall n (a : int n), a `(+) Z2u n 0 = a.
Parameter int_xorC : forall n (a b : int n), a `(+) b = b `(+) a.
Parameter int_xorA : forall n (a b c : int n), (a `(+) b) `(+) c = a `(+) (b `(+) c).
(** x (+) x = 0 *)
Parameter int_xor_self : forall n (a : int n), a `(+) a = Z2u n 0.

Parameter int_not : forall n, int n -> int n.
(** x & -1 = x *)
Parameter int_and_1s : forall n a, a `& int_not (Z2u n 0) = a.
(** not (x | y) = not x & not y *)
Parameter int_not_or : forall n (a b : int n), int_not (a `|` b) = int_not a `& int_not b.
(** x (+) -1 = not x *)
Parameter int_xor_1s : forall n (a : int n), a `(+) int_not (Z2u n 0) = int_not a.

Parameter cplt2 : forall n, int n -> int n.
Parameter cplt2_zero : forall n, cplt2 (Z2u n 0) = Z2u n 0.
Parameter cplt2_1s : forall n, cplt2 (int_not (Z2u n 0)) = Z2u n 1.
Parameter not_add_1_cplt2: forall n (v : int n), (n > 1)%nat -> int_not v `+ Z2u n 1 = cplt2 v.
Parameter cplt2_inj : forall n (a b : int n), cplt2 a = cplt2 b -> a = b.
Parameter sub_cplt2 : forall n (a b : int n.+1), a `- b = a `+ cplt2 b.

Parameter concat : forall n m (a : int n) (b : int m), int (n + m).
Notation "a '`||' b " := (concat a b) : machine_int_scope.
Parameter zext_concat : forall n (a : int n) m, zext m a = `( 0 )_ m `|| a.
Parameter concatA : forall k m n (a : int k) (b : int m) (c : int n),
  a `|| b `|| c = castA (@addnA _ _ _) (a `|| (b `|| c)).

Parameter or_concat : forall n (a : int n) (b : int n) k (Hkn : (k <= n)%nat),
  u2Z a < 2 ^^ k ->
  b `% k = Z2u k 0 ->
  (b `|` a) = cast_subnK Hkn ((shr_shrink k b) `|| (a `% k)).
Parameter rem_concat : forall n (a : int n) m (b : int m), (a `|| b) `% m = b.
Parameter concat_shl : forall n (a : int n) m,
  a `|| Z2u m 0 = castC (@addnC _ _) (zext m a `<< m).

(* NB: Parameter shrl_shr_shrink : forall n (a : int n) k,
  (k <= n)%nat -> (Z2u k 0 `|| shr_shrink k a) = shrl k a. does not type*)

(** interpretation of int as unsigned integers and related properties *)
Parameter u2Z_add : forall n (a b : int n), u2Z a + u2Z b < 2 ^^ n -> u2Z (a `+ b) = u2Z a + u2Z b.
Parameter u2Z_add_overflow : forall n (a b : int n), 2 ^^ n <= u2Z a + u2Z b -> u2Z (a `+ b) + 2 ^^ n = u2Z a + u2Z b.
Parameter u2Z_sub : forall n (a b : int n), u2Z a >= u2Z b -> u2Z (a `- b) = u2Z a - u2Z b.
Parameter u2Z_sub_overflow : forall n (a b : int n), u2Z a < u2Z b -> u2Z (a `- b) = u2Z a + 2 ^^ n - u2Z b.
Parameter u2Z_mul : forall n (a b : int n), u2Z a * u2Z b < 2 ^^ n -> u2Z (mul a b) = u2Z a * u2Z b.
Parameter u2Z_umul: forall n (a b : int n), u2Z (a `* b) = u2Z a * u2Z b.

(* x << k = |_ 2^k x _| *)
Parameter u2Z_shl : forall k n (x : int n) m, (k + m <= n)%nat -> u2Z x < 2 ^^ m ->
  u2Z (x `<< k) = u2Z x * 2 ^^ k.
Parameter u2Z_shl' : forall n (x : int n), forall m, u2Z x < 2 ^^ m -> forall k, (k + m <= n)%nat ->
  u2Z (x `<< k) <= 2 ^^ (m + k) - 2 ^^ k.
Parameter u2Z_shl_overflow : forall k n (x : int n), (k >= n)%nat -> u2Z (x `<< k) = 0.
Parameter cast_shl : forall n k (a : int k) (Hkn : (k <= n)%nat) m (kmn : (k + m <= n)%nat),
  cast_subnK Hkn (zext (n - k) a `<< m) = (cast_subnK Hkn (zext (n - k) a )) `<< m.
Parameter u2Z_shl_Zmod : forall n (a : int n) k, (k < n)%nat ->
  u2Z (a `<< k) = (u2Z a * 2 ^^ k) mod 2 ^^ n.
Parameter u2Z_shl_rem : forall n (a : int n) k, u2Z (a `<< k) = 2 ^^ k * u2Z (a `% (n - k)).

Parameter u2Z_shl_ext : forall k n (x : int n), u2Z (shl_ext k x) = u2Z x * 2 ^^ k.
Parameter u2Z_shl_ext' : forall n (x : int n), forall m, u2Z x < 2 ^^ m -> forall k,
  u2Z (shl_ext k x) <= 2 ^^ (m + k) - 2 ^^ k.
Parameter u2Z_shl_ext'' : forall l (x : int l), forall k, u2Z x < 2 ^^ k -> forall n,
  u2Z (shl_ext n x) + 2 ^^ n <= 2 ^^ (k + n).

Parameter Zle_u2Z_shr_shrink : forall n (a : int n) k,
  u2Z (shr_shrink k a) * 2 ^^ k <= u2Z a.
Parameter u2Z_shr_shrink : forall l (x : int l) n, (l >= n)%nat ->
  u2Z (shr_shrink n x) * 2 ^^ n + u2Z (x `% n) = u2Z x.
Parameter u2Z_shr_shrink': forall l (x : int l) n, (l >= n)%nat ->
  u2Z (shr_shrink n x) * 2 ^^ n = u2Z x - u2Z (x `% n).

Parameter u2Z_shrl : forall {n} (x : int n) k, (n >= k)%nat ->
  u2Z (x `>> k) * 2 ^^ k + u2Z (x `% k) = u2Z x.

Parameter shrl_lt : forall n (a : int n) m, u2Z (a `>> m) < 2 ^^ (n - m).

Parameter u2Z_or : forall m n (a : int m) (b : int n),
  u2Z ((a `|| Z2u n 0) `|` zext m b) = (u2Z a * 2 ^^ n + u2Z b)%Z.

Parameter u2Z_rem : forall n (x : int n) k, (n >= k)%nat -> u2Z (x `% k) = u2Z x - u2Z (shr_shrink k x) * 2 ^^ k.
Parameter u2Z_rem' : forall n (a : int n) k, u2Z a < 2 ^^ k -> u2Z (a `% k) = u2Z a.

Parameter u2Z_rem'' : forall {n} (a : int n) k a', u2Z a = 2 ^^ k.+1 * a' -> u2Z (a `% k.+1) = 0.

Parameter u2Z_rem_zext : forall n (a : int n) k m, u2Z (zext k a `% m) = u2Z (a `% m).

Parameter u2Z_concat : forall n l (a : int n) (b : int l), u2Z (a `|| b) = u2Z a * 2 ^^ l + u2Z b.

Parameter lt_n2Zlt : forall n (a b : int n), lt_n a b -> u2Z a < u2Z b.
Parameter le_n2Zle : forall n (a b:int n), a `<= b -> u2Z a <= u2Z b.
Parameter Zlt2lt_n : forall n (a b : int n), u2Z a < u2Z b -> lt_n a b.
Parameter Zle2le_n : forall n (a b:int n), u2Z a <= u2Z b -> a `<= b.

Parameter s2Z : forall n, int n -> Z.
Parameter s2Zc : forall n, int n -> Z.
Parameter s2ZE : forall n (a : int n), s2Z a = s2Zc a.
Parameter max_s2Z : forall n (a : int n), s2Z a < 2 ^^ n.-1.
Parameter min_s2Z : forall n (a : int n.+1), - 2 ^^ n <= s2Z a.
Parameter s2Z_zext : forall k n (a : int n), (0 < k)%nat -> s2Z (zext k a) = u2Z a.
Arguments s2Z_zext _ [n] _ _.
Parameter s2Z_inj : forall n (v w : int n), s2Z v = s2Z w -> v = w.
Parameter s2Z_cast : forall (f : nat -> nat -> nat) (P : nat -> nat -> Type)
  (H : forall k n : nat, P k n -> f k n = n) k n (Hkn : P k n) a,
  s2Z (cast H Hkn a) = s2Z a.
Parameter s2Z_castA : forall k m n (a : int (k + (m + n))),
                    s2Z (castA (@addnA _ _ _) a) = s2Z a.

Parameter weird : forall n (v : int n.+1), Prop.
Parameter weirdE : forall n (a : int n.+1), weird a <-> u2Z a = 2 ^^ n.
Parameter weirdE2 : forall n (a : int n.+1), weird a <-> s2Z a = - 2 ^^ n.

Parameter s2Z_cplt2: forall n (v : int n.+1), ~ weird v -> s2Z (cplt2 v) = - (s2Z v).
Parameter sext_s2Z : forall n (v : int n) k, s2Z (sext k v) = s2Z v.

(** Z2s n z builds a signed machine integer of decimal value z and length n (if possible). *)
Parameter Z2s : forall n (z : Z), int n.
Parameter Z2sc : forall n (z : Z), int n.
Notation "'`(' x ')s_' n" := (Z2s n x) : machine_int_scope.
Notation "'`(' x ')sc_' n" := (Z2sc n x) : machine_int_scope.
Parameter Z2sE : forall n (z : Z), `( z )s_ n = `( z )sc_ n.
Parameter Z2sK : forall z m, - 2 ^^ m <= z < 2 ^^ m -> s2Z (`( z )s_m.+1) = z.
Parameter Z2s_dis : forall n a b, - 2 ^^ n <= a < 2 ^^ n -> - 2 ^^ n <= b < 2 ^^ n ->
  a <> b -> `( a )s_n.+1 <> `( b )s_n.+1.
Parameter int_even_and_1_converse : forall n (a : int n), a `& Z2u n 1 = Z2u n 0 -> Zeven (s2Z a).
Parameter sext_Z2s : forall m z n, - 2 ^^ m <= z < 2 ^^ m -> sext n (`( z )s_m.+1) = `( z)s_(m.+1 + n).

(** relations between u2Z and s2Z/Z2s *)

Parameter s2Z_u2Z_pos : forall n (a : int n), 0 <= s2Z a -> s2Z a = u2Z a.
Parameter s2Z_u2Z_pos' : forall n (a : int n), 0 <= u2Z a < 2 ^^ n.-1 -> s2Z a = u2Z a.
Parameter s2Z_u2Z_neg : forall n (a : int n), s2Z a < 0 -> u2Z a = s2Z a + 2^^n.
Parameter Z2s_weird : forall n, u2Z (`(- 2 ^^ n)s_n.+1) = 2 ^^ n.
Parameter u2Z_Z2s_neg : forall z n, - 2 ^^ n.-1 <= z < 0 -> u2Z (`( z )s_ n)  = 2 ^^ n + z.
Parameter u2Z_Z2s_pos : forall z n, 0 <= z < 2 ^^ n.-1 -> u2Z (`( z )s_ n)  = z.

(** interpretation of int as signed integers and related properties *)
Parameter s2Z_add: forall n (a b : int n.+1), - 2 ^^ n <= s2Z a + s2Z b < 2 ^^ n -> s2Z (a `+ b) = s2Z a + s2Z b.
Parameter s2Z_sub: forall n (a b : int n.+1), (- 2 ^^ n <= s2Z a - s2Z b < 2 ^^ n)%Z -> s2Z (a `- b) = (s2Z a - s2Z b)%Z.
Parameter Z2s_Z2u_k : forall n k, 0 <= k < 2 ^^ n -> `( k )s_ n = `( k )_ n.

Parameter s2Z_smul : forall n (a b : int n), s2Z (smul a b) = s2Z a * s2Z b.
Parameter s2Z_shl : forall m k n (x : int n), (k + m.+1 <= n)%nat -> - 2 ^^ m <= s2Z x < 2 ^^ m ->
  s2Z (shl k x) = s2Z x * 2 ^^ k.
Parameter bits_shra_neg : forall n (a : int n.+1) m, s2Z a < 0 ->
  (n <= m)%nat ->
  bits (shra m a) = bits.ones n.+1.
Parameter bits_shra_nonneg : forall n (a : int n.+1) m, 0 <= s2Z a ->
  (n <= m)%nat ->
  bits (shra m a) = bits.zeros n.+1.
Parameter s2Z_shra_neg : forall n (a : int n.+1) m, s2Z a < 0 -> (n <= m)%nat ->
  shra m a = int_not (Z2u n.+1 0).
Parameter s2Z_shra_pos : forall n (a : int n.+1) m, 0 <= s2Z a -> (n <= m)%nat ->
  shra m a = Z2u n.+1 0.
Parameter le0concat : forall m n (a : int n), (0 <= s2Z ( `( 0 )_m.+1 `|| a))%Z.

Parameter shrl_sign_bit : forall (n : nat) (a : int (2 ^ n)),
 a `>> (2 ^ n - 1) = Z2u (2 ^ n) 0 \/ a `>> (2 ^ n - 1) = Z2u (2 ^ n) 1.
(* TODO: remove this entry? *)
Parameter bZsgn_Zsgn_s2Z : forall (n : nat) (a : int (2 ^ n)), u2Z a <> 0 ->
  bZsgn (u2Z (a `>> (2 ^ n - 1))) = sgZ (s2Z a).
Parameter le0_or : forall n (a b : int n.+1),
  0 <=? s2Z a -> 0 <=? s2Z b -> 0 <=? s2Z (a `|` b).

Local Close Scope machine_int_scope.

Parameter int_break : forall n k q, n = (q * k)%nat -> forall (a : int n), list (int k).
Parameter size_int_break : forall (n k q : nat) (Hn : n = (q * k.+1)%nat) (a : int n),
    size (int_break Hn a) = q.
Parameter int_break_cons :
  forall n k q v (H : n = (q.+1 * k)%nat) (H' : (n - k)%nat = (q * k)%nat),
  k <> O ->
  int_break H v = Z2u k (u2Z v / 2 ^^ (n - k)) :: int_break H' (Z2u (n - k) (u2Z v)).
Parameter int_flat : forall n k q, n = (q * k)%nat -> list (int k) -> option (int n).
Parameter int_flat_Some : forall n k q (H : n = (q * k)%nat) (l : list (int k)),
  size l = q -> { x | int_flat H l = Some x }.
Parameter int_flat_None : forall n k q (H : n = (q * k)%nat) (l : list (int k)),
  k <> O -> size l <> q -> int_flat H l = None.
Parameter int_flat_ok :
  forall n k q (H: n = (q * k)%nat) (l : list (int k)) (Hl : size l = q), int n.
Parameter int_flat_ok_id : forall n (a : int n) H H',
    @int_flat_ok n n 1 H (a :: nil) H' = a.
Parameter int_flat_take : forall n k q (H : n = (q * k)%nat) (l : list (int k)) x x',
  k <> O -> int_flat H l = Some x ->
  int_flat H (take n l) = Some x' -> x = x'.
Parameter int_flat_inj : forall n k l1 l2 nk x,
  n != O -> forall (H : nk = (k * n)%nat),
  int_flat H l1 = Some x ->
  int_flat H l2 = Some x ->
  l1 = l2.

Parameter int_flat_ok_inj : forall n k q H l1 Hl1 l2 Hl2, (k != 0)%nat ->
  @int_flat_ok n k q H l1 Hl1 = @int_flat_ok n k q H l2 Hl2 ->
  l1 = l2.

Parameter int_flat_int_flat_ok : forall n k q (Hn : (n = q * k)%nat) a a' H,
  @int_flat n k q Hn a = Some a' -> @int_flat_ok n k q Hn a H = a'.
Parameter int_flat_ok_int_flat : forall (n k q : nat) (Hn : (n = q * k)%nat)
  (a : list (int k)) (a' : int n) (H : size a = q),
  int_flat_ok Hn H = a' -> int_flat Hn a = Some a'.

Parameter int_flat_int_break : forall n k q (a : int n) (Hn : (n = q * k)%nat),
  int_flat Hn (int_break Hn a) = Some a.
Parameter int_flat_break :
  forall q n k (a : list (int k.+1)) (b : int n) (Hn : (n = q * k.+1)%nat),
  int_flat Hn a = Some b -> int_break Hn b = a.
Parameter int_break_flat : forall (n k q : nat) (Hn : (n = q * k)%nat)
  (a : list (int k)) (a' : int n) (H : size a = q),
  int_break Hn a' = a -> int_flat Hn a = Some a'.
Parameter int_break_0 : forall q n k (H : n = (q * k.+1)%nat),
  int_break H (Z2u n 0) = nseq q (Z2u k.+1 0).
Parameter int_break_inj : forall n k nk (l1 l2 : int nk) ,
  n <> O -> forall (H : nk = (k * n)%nat),
  int_break H l1 = int_break H l2 ->
  l1 = l2.

End MACHINE_INT.

Module MachineInt : MACHINE_INT
with Definition u2Zc := fun n (a : int n) => match a with mk_int lst _ => bitZ.u2Z lst end
with Definition s2Zc := fun n (a : int n) => match a with mk_int lst _ => bitZ.s2Z lst end
with Definition Z2uc := fun n (l : Z) => mk_int (bits.size_adjust_u n (bitZ.Z2u l))
with Definition Z2sc := fun n (l : Z) => mk_int (bits.size_adjust_s n (bitZ.Z2s l)).

Definition make_int : forall (n : nat) (lst : list bool), size lst = n -> int n := mk_int.

Lemma mk_int_pi : forall n l (H : size l = n) l' (H' : size l' = n),
  l = l' -> mk_int H = mk_int H'.
Proof. move=> n l H l' H' H''; subst l; by rewrite (proof_irrelevance _ H H'). Qed.

Lemma mk_int_pi' : forall n l (H : size l = n) n' l' (H' : size l' = n') (n_n' : n = n'),
  l = l' -> eq_rect n int (mk_int H) _ n_n' = mk_int H'.
Proof.
move=> n l H n' l' H' n_n' H''; subst l'.
move: (n_n') H H'.
rewrite n_n' => {n_n'}n_n'.
have : n_n' = refl_equal n'.
apply proof_irrelevance.
rewrite /eq_rect.
move=> -> H H'; by apply mk_int_pi.
Qed.

Definition int_lst n (b : int n) := match b with mk_int lst _ => lst end.

Lemma mk_int_pi'' : forall n l (H : size l = n) n' (n_n' : n = n'),
  int_lst (eq_rect n int (mk_int H) _ n_n') = l.
Proof.
move=> n l H n' n_n'.
move: (n_n') H.
rewrite n_n' => {n_n'}n_n'.
have : n_n' = refl_equal n' by apply proof_irrelevance.
by move=> ->.
Qed.

Definition bits n (b : int n) := rev (int_lst b).

Definition int_prf n (b : int n) : size (int_lst b) = n :=
  match b return size (int_lst b) = n with mk_int l prf => prf end.

Lemma dec_int : forall l (a b : int l), { a = b } + { a <> b }.
Proof.
move=> l [a Ha] [b Hb] /=.
elim (bits.dec_equ_lst_bit a b) => H.
- left; subst a; by apply: mk_int_pi.
- right; by move=> [H'].
Qed.

Definition cast {f : nat -> nat -> nat} {P}
  (HPf : forall k n, P k n -> f k n = n) {k n} (HP : P k n) :
  int (f k n) -> int n.
Proof. exact (fun x => eq_rect (f k n) _ x n (HPf k n HP)). Defined.

Definition cast_subnK {k n : nat} (H : (k <= n)%nat) := cast subnK H.
Definition cast_subnKC {k n : nat} (H : (k <= n)%nat) := cast subnKC H.

Definition castC {n m : nat} (H : n = m) : int n -> int m.
move=> a.
exact match a with
 | mk_int lst e =>
     mk_int
       ((fun x : size lst = n =>
         eq_ind n (fun y : nat => size lst = y)
           x m H) e)
 end.
Defined.

Definition castA {n m k} (H : (n + (m + k) = n + m + k)%nat) : int (n + (m + k)) -> int (n + m + k).
move=> a.
exact match a with
 | mk_int lst e =>
     mk_int
       ((fun x : size lst = (n + (m + k))%nat =>
         eq_ind (n + (m + k))%nat (fun y : nat => size lst = y)
           x (n + m + k)%nat H) e)
 end.
Defined.

Definition u2Z len (a : int len) : Z := match a with mk_int lst _ => bitZ.u2Z lst end.
Definition u2Zc len (a : int len) : Z := match a with mk_int lst _ => bitZ.u2Z lst end.
Lemma u2ZE : forall n (a : int n), u2Z a = u2Zc a. Proof. done. Qed.

Lemma max_u2Z : forall l (a : int l), u2Z a < 2 ^^ l.
Proof. move=> l [lst H] /=. apply bitZ.max_u2Z; by rewrite H. Qed.

Lemma min_u2Z n : forall (a : int n), 0 <= u2Z a.
Proof. case=> l H /=; by apply bitZ.min_u2Z. Qed.
Arguments min_u2Z [n] _ _.

Lemma u2Z_inj : forall l (v w : int l), u2Z v = u2Z w -> v = w.
Proof.
move=> l [vl Hv] [wl Hw] /= H.
apply: mk_int_pi.
by eapply bitZ.u2Z_inj; eauto.
Qed.

Lemma u2Z_cast : forall (f : nat -> nat -> nat) (P : nat -> nat -> Type)
  (H : forall k n : nat, P k n -> f k n = n) k n (Hkn : P k n) a,
  u2Z (cast H Hkn a) = u2Z a.
Proof.
move=> f P H k n Hkn [a Ha] /=.
rewrite /cast /eq_rect.
move: (H k n Hkn).
move: Ha.
rewrite H // => Ha H0.
suff : H0 = refl_equal n by move=> ->.
by apply proof_irrelevance.
Qed.

Lemma u2Z_eq_rect : forall n (a : int n) m (H : n = m),
  u2Z (eq_rect _ _ a _ H) = u2Z a.
Proof.
move=> n [a Ha] /= m H.
rewrite (@mk_int_pi' n a Ha m a) //.
by subst.
Qed.

Lemma u2Z_castC : forall m n (a : int n) (H : n = m), u2Z (castC H a) = u2Z a.
Proof. by move=> m n []. Qed.

Lemma u2Z_castA : forall n m k (a : int _) (H : (n + (m + k) = n + m + k)%nat), u2Z (castA H a) = u2Z a.
Proof. by move=> n m k []. Qed.

Lemma size_bits : forall n (a : int n), size (bits a) = n.
Proof. move=> n [a H]. by rewrite /bits size_rev. Qed.

Definition bits2u n (l : list bool) : int n := mk_int (bits.size_adjust_u n l).

Lemma u2Z_bits2u_u2Z n l : size l = n -> u2Z (bits2u n l) = bitZ.u2Z l.
Proof.
move=> H.
rewrite /bits2u /= /bits.adjust_u.
have -> : (size l < n)%nat = false by rewrite H ltnn.
rewrite (bitZ.skipn_Zmod (size l)) //; last first.
  by rewrite H /= -minusE /= -minus_n_n.
have -> : (size l - (size l - n) = n)%nat.
  rewrite subnBA //; last by rewrite H.
  by rewrite addnC addnK.
rewrite Zmod_small //.
split; [by apply bitZ.min_u2Z | apply bitZ.max_u2Z; by rewrite H].
Qed.

Definition Z2u n (l : Z) : int n := mk_int (bits.size_adjust_u n (bitZ.Z2u l)).
Definition Z2uc n (l : Z) : int n := mk_int (bits.size_adjust_u n (bitZ.Z2u l)).
Local Notation "'`(' x ')_' n" := (Z2u n x).
Notation "'`(' x ')c_' n" := (Z2uc n x) : machine_int_scope.
Local Open Scope machine_int_scope.

Lemma Z2uE : forall n z, `( z )_n = `( z )c_ n. Proof. done. Qed.

Lemma Z2uK z m : 0 <= z < 2 ^^ m -> u2Z `( z )_m = z.
Proof.
case=> H1 H2.
rewrite /u2Z /Z2u.
destruct z as [|p|p].
- by rewrite /= bits.adjust_u_nil bitZ.u2Z_zeros.
- destruct m as [|m].
  + by destruct p.
  + rewrite bitZ.adjust_u2Z; last first.
      apply bitZ.max_u2Z => /=.
      rewrite size_rev.
      by apply bitZ.pos2lst_len.
    by apply bitZ.Z2uK.
- move: (Zlt_neg_0 p) => ?; omega.
Qed.

Lemma u2Z_Z2u_Zmod' : forall z n, 2 ^^ n <= z -> u2Z `( z )_n = z mod (2 ^^ n).
Proof.
move=> z n H.
rewrite /u2Z /Z2u.
destruct z as [|p|p].
- by rewrite /= bits.adjust_u_nil bitZ.u2Z_zeros.
- by rewrite bitZ.adjust_u2Z_overflow bitZ.Z2uK.
- move: (Zlt_neg_0 p) (expZ_gt0 n) => ? ?; omega.
Qed.

Lemma u2Z_Z2u_Zmod : forall z n, 0 <= z -> u2Z (Z2u n z) = z mod (2 ^^ n).
Proof.
move=> z n H.
case: (Z_lt_le_dec z (2 ^^ n)) => X.
by rewrite Zmod_small // Z2uK.
by apply u2Z_Z2u_Zmod'.
Qed.

Lemma u2Z_Z2u_neg: forall z n, z < 0 -> u2Z (Z2u n z) = 0.
Proof. case=> //=. move=> p n _; by rewrite bits.adjust_u_nil bitZ.u2Z_zeros. Qed.

Lemma Z2u_dis l a b : 0 <= a < 2 ^^ l -> 0 <= b < 2 ^^ l ->
  a <> b -> Z2u l a <> Z2u l b.
Proof.
move=> Ha Hb Hab; contradict Hab.
by rewrite -(Z2uK Ha) // -(Z2uK Hb) // Hab.
Qed.

Lemma Z2u_u2Z : forall n (a : int n), Z2u n (u2Z a) = a.
Proof.
move=> n [lst Hlst] /=.
rewrite /Z2u.
apply mk_int_pi.
rewrite (bitZ.u2ZK _ _ Hlst).
have X : (size (bits.erase_leading_zeros lst) <= n)%nat.
  by apply bits.size_erase_leading_zeros.
rewrite (bits.adjust_u_S'' n _ (bits.erase_leading_zeros lst) (refl_equal _)).
by rewrite bits.erase_leading_zeros_prop.
exact X.
Qed.

Lemma bits_zeros : forall n, bits (Z2u n 0) = bits.zeros n.
Proof. move=> n /=. by rewrite /bits /= bits.adjust_u_nil bits.rev_zeros. Qed.

Lemma Z2u_inj {n} : forall a b, (0 <= a < 2 ^^ n)%Z -> (0 <= b < 2 ^^ n)%Z ->
  Z2u n a = Z2u n b -> a = b.
Proof.
move=> a b Ha Hb ab.
have {ab}ab : u2Z (Z2u n a) = u2Z (Z2u n b) by rewrite ab.
by rewrite !Z2uK in ab.
Qed.

Definition zext m n (a : int n) : int (m + n) :=
  mk_int (bits.size_zext n (int_lst a) m (int_prf a)).

Lemma zext_zext n (a : int n) m k : castA (@addnA _ _ _) (zext k (zext m a)) = (zext (k + m) a).
Proof. apply mk_int_pi => /=. by rewrite /bits.zext catA bits.zeros_app. Qed.

Lemma zext_Z2u n m m' : n < 2 ^^ m -> zext m' (Z2u m.+1 n) = Z2u (m' + m.+1) n.
Proof. move=> Hn. apply mk_int_pi => //=. by rewrite bitZ.zext_Z2u // -addSn addnC. Qed.

Lemma u2Z_zext : forall (k : nat) l (a : int l), u2Z (zext k a) = u2Z a.
Proof. move=> k l [a Ha] //. rewrite /u2Z /zext /=. by elim: k. Qed.

Lemma size_sext' m l k : size l = k -> size (bits.sext m l) = (k + m)%nat.
Proof. move=> <-. by rewrite bits.size_sext. Qed.

Definition sext (m: nat) n (a: int n) : int (n + m) :=
  mk_int (@size_sext' m (int_lst a) n (int_prf a)).

Lemma u2Z_sext : forall l (v:int l) n, 0 <= u2Z v < 2 ^^ l.-1 ->
  u2Z (sext n v) = u2Z v.
Proof. move=> l [v Hv] /= n H. by eapply bitZ.sext_u2Z; eauto. Qed.

Lemma sext_Z2u n m m' : n < 2 ^^ m -> sext m' (Z2u m.+1 n) = Z2u (m.+1 + m') n.
Proof. move=> Hn. apply mk_int_pi => //=. by rewrite bitZ.sext_Z2u. Qed.

Definition lt_n n (a b : int n) : bool := bits.ult (int_lst a) (int_lst b).
Notation "a '`<' b" := (lt_n a b) : machine_int_scope.

Definition le_n n (a b : int n) : bool := bits.ule (int_lst a) (int_lst b).
Notation "a '`<=' b" := (le_n a b) : machine_int_scope.

Lemma le_n_refl : forall n (a : int n), a `<= a.
Proof. move=> n a; rewrite /le_n /bits.ule. apply/orP; right; by apply bits.listbit_eq_refl. Qed.

Lemma le_nE : forall n (a b : int n), a `<= b -> a = b \/ a `< b.
Proof.
move=> n a b; rewrite /le_n /bits.ule.
case/orP => H.
right; by rewrite /lt_n.
left; move/bits.listbit_eq_eq in H.
destruct a; destruct b.
rewrite /= in H.
by apply mk_int_pi.
Qed.

Lemma lt_nW : forall n (a b : int n), a `< b -> a `<= b.
Proof. move=> n a b H; rewrite /le_n /bits.ule; apply/orP; by auto. Qed.

Definition add l (a b : int l) : int l := mk_int
  (bits.size_add l (int_lst a) (int_lst b) (int_prf a) (int_prf b) false).
Notation "a '`+' b" := (add a b) : machine_int_scope.

Lemma addC n : forall (a b : int n), a `+ b = b `+ a.
Proof. move=> [a Ha] [b Hb] /=. apply mk_int_pi => /=. by rewrite bits.addC. Qed.

Lemma addA n : forall (a b c : int n), (a `+ b) `+ c = a `+ (b `+ c).
Proof. move=> [a Ha] [b Hb] [c Hc]. apply mk_int_pi. by apply bits.addA with n. Qed.

Lemma addi0 : forall l (a : int l), a `+ Z2u l 0 = a.
Proof.
move=> l [lst prf].
rewrite /add /=.
apply mk_int_pi.
by rewrite bits.adjust_u_nil bits.addl0 // prf.
Qed.

Definition sub n (a b : int n) : int n := mk_int
  (bits.size_sub n (int_lst a) (int_lst b) false (int_prf a) (int_prf b)).
Notation "a '`-' b" := (sub a b) : machine_int_scope.

(** unsigned multiplication with truncation *)
Definition mul n (a b : int n) : int n := mk_int
  (bits.size_adjust_u n (bits.umul (int_lst a) (int_lst b))).

(** unsigned multiplication (traditional one, without truncation) *)
Definition umul : forall l (a b : int l), int (l + l).
Proof.
move=> l [a Ha] [b Hb].
have H : size (bits.umul a b) = (l + l)%nat by rewrite bits.size_umul Ha Hb.
exact (mk_int H).
Defined.
Notation "a '`*' b" := (umul a b) : machine_int_scope.

Lemma umulC : forall l (a b : int l), a `* b = b `* a.
Proof.
move=> [|l] [ [|a0 a] Ha] [ [|b0 b] Hb] //.
rewrite (proof_irrelevance _ Ha Hb) // /umul.
apply mk_int_pi.
by apply (bits.umulC l.+1).
Qed.

Lemma umul_1 : forall l (x : int l), x `* `( 1 )_ l = zext l x.
Proof.
move=> l [lst prf].
rewrite /= /zext.
apply mk_int_pi => /=.
destruct l.
- by destruct lst.
- by rewrite (bits.adjust_u_S'' (l.+1) 1) //= subSS subn0 bits.umull1.
Qed.

Lemma umul_0 : forall n (x : int n), x `* `( 0 )_ n  = `( 0 )_ (n + n).
Proof.
move=> n [x Hx] /=.
apply mk_int_pi => /=.
by rewrite 2!bits.adjust_u_nil bits.umull0 Hx.
Qed.

(** signed multiplication *)
Lemma smul_lst_size_size : forall n (a b : int n),
  (size (bits.smul (int_lst a) (int_lst b)) = 2 * n)%nat.
Proof. move=> n [a Ha] [b Hb] /=; by rewrite (bits.size_smul n). Qed.

Definition smul n (a b : int n) : int (2 * n) := mk_int (smul_lst_size_size a b).

(** remainder *)
Definition rem n m (a : int m) : int n.
Proof. case: a => a Ha. exists (bits.adjust_u a n); by rewrite bits.size_adjust_u. Defined.
Notation "a '`%' n" := (rem n a) : machine_int_scope.

Lemma rem_Zpower : forall n k, (k < n)%nat -> Z2u n (2 ^^ k) `% k = Z2u k 0.
Proof.
move=> n k Hkn.
rewrite /Z2u.
apply mk_int_pi.
rewrite bits.adjust_u_nil bitZ.Z2u_2_Zpower /bits.adjust_u.
rewrite [size (_ :: _)]/= !size_nseq.
have [X|X] : (k.+1 < n \/ k.+1 < n = false)%nat by case (k.+1 < n)%nat; auto.
- rewrite X.
  rewrite (bits.size_zext k.+1); last by rewrite /= size_nseq.
  rewrite subnK //.
  have Y : (n < k = false)%nat. by apply/negbTE; rewrite -leqNgt ltnW.
  rewrite Y /bits.zext.
  rewrite -cat1s catA drop_size_cat //.
  by rewrite size_cat size_nseq addn1 -subSn //.
- rewrite X.
  rewrite size_drop [size (_ :: _)]/= size_nseq subKn; last by rewrite leqNgt X.
  rewrite ltnNge ltnW //.
  rewrite [drop]lock /= -lock.
  have -> : (succn k - n = 0)%nat.
    apply/eqP.
    by rewrite subn_eq0.
  rewrite drop0.
  have -> : n = succn k.
    move/negbT in X.
    rewrite -leqNgt in X.
    apply/eqP; rewrite eqn_leq.
    by rewrite X Hkn.
  by rewrite subSn // subnn /= drop0.
Qed.

Definition shl m n (a: int n) : int n := mk_int (bits.size_shl m n (int_lst a) (int_prf a)).
Notation "a '`<<' n" := (shl n a) : machine_int_scope.

Lemma shl_zero : forall n m,  Z2u n 0 `<< m = Z2u n 0.
Proof. move=> n m; apply mk_int_pi => /=; by rewrite bits.adjust_u_nil bits.shl_zeros. Qed.

Lemma shl_1 : forall n k, (k <= n)%nat -> Z2u n 1 `<< k = Z2u n (2 ^^ k).
Proof.
move=> n k Hkn.
apply mk_int_pi => /=.
rewrite bitZ.Z2u_2_Zpower /bits.adjust_u /= size_nseq.
have [X|X] : (1 < n \/ 1 < n = false)%nat by destruct (1 < n)%nat; auto.
- rewrite X.
  have [Y|Y] : (k.+1 < n \/ k.+1 < n = false)%nat by destruct (k.+1 < n)%nat; auto.
  + rewrite Y /bits.zext (bits.shl_app' _ (n - 1)); last 2 first.
      by rewrite size_nseq.
      move/ltP in Y.
      apply/leP.
      rewrite -minusE; omega.
    rewrite bits.skipn_zeros (_ : _ - _ - _ = n - k.+1)%nat //.
    move/ltP in Y.
    rewrite -!minusE; omega.
  + rewrite Y.
    have [Z|Z] : (k = n \/ k = n-1)%nat.
      rewrite -minusE; move/ltP in X; move/ltP in Y; move/leP in Hkn; omega.
    * subst k.
      rewrite (_ : n.+1 - n = 1)%nat /=.
      rewrite (bits.shl_overflow _ n) // ?drop0 // (bits.size_zext 1) //.
      rewrite subn1 addn1 prednK //.
      by apply: ltn_trans X.
      by rewrite subSn // subnn.
    * subst k.
      rewrite (_ : (n-1).+1 - n = 0)%nat /=; last first.
        rewrite -!minusE.
        move/ltP in X; omega.
      rewrite /bits.zext (bits.shl_app' _ (n - 1)); last 2 first.
        by rewrite size_nseq.
        by apply leqnn.
      by rewrite bits.skipn_zeros subnn.
- rewrite X.
  move/leP in Hkn.
  destruct n => /=.
  move/leP in Hkn; by destruct k.
  destruct n => //.
  destruct k => //.
  move/leP in Hkn; by destruct k.
Qed.

Lemma bits_shl_1 n m : (m < n)%nat ->
  bits (Z2u n 1 `<< m) = bits.zeros m ++ true :: nil ++ bits.zeros (n - m - 1).
Proof.
move=> Hmn.
rewrite /Z2u /bits /bits.adjust_u /=.
case: ifP => X.
- rewrite /bits.zext (bits.shl_app' m (n - 1)); last 2 first.
    + by rewrite size_nseq.
    + by rewrite -(leq_add2r 1) 2!addn1 subn1 prednK // (ltn_trans _ X).
  rewrite rev_cat /= rev_cons -cats1 bits.rev_zeros bits.skipn_zeros bits.rev_zeros -catA /=.
  by rewrite -subnDA add1n -subnDA addn1.
- move/ltP : Hmn => Hmn.
  destruct n => //=.
  by move/ltP in Hmn; destruct m.
  move/ltP in Hmn; destruct n => //=.
  by destruct m.
Qed.

Lemma shl_rem_m : forall n (a : int n) m, (m <= n)%nat -> (a `<< m) `% m = Z2u m 0.
Proof.
move=> n [a Ha] m Hmn /=.
apply mk_int_pi => /=.
rewrite bits.adjust_u_nil /bits.adjust_u (bits.size_shl m n) //.
rewrite leqNgt in Hmn.
rewrite (negbTE Hmn).
subst n.
rewrite -leqNgt in Hmn.
rewrite -(cat_take_drop m a) size_cat.
rewrite bits.shl_cat; last first.
  rewrite size_take.
  case: ifP => // /negbT.
  rewrite -leqNgt => H1.
  by apply/eqP; rewrite eqn_leq H1.
rewrite drop_size_cat // size_drop size_take.
case: ifP => // H1.
  by rewrite addnC addnK.
move/negbT in H1.
rewrite -leqNgt in H1.
have /eqP <- : m == size a by rewrite eqn_leq Hmn H1.
by rewrite !(subnn, addn0).
Qed.

Definition shl_ext m n (a : int n) : int (m + n) :=
  mk_int (bits.size_shl_ext n (int_lst a) m (int_prf a)).

Definition shrl m n (a : int n) := mk_int (bits.size_shrl n m (int_lst a) (int_prf a)).
Notation "a '`>>' k" := (shrl k a) : machine_int_scope.

Lemma shrl_comp : forall m k n (a : int n), (a `>> k) `>> m = a `>> (k + m).
Proof. move=> m k n [a Ha] /=. apply mk_int_pi => /=. by rewrite bits.shrl_comp addnC. Qed.

Lemma shrl_0 : forall n (a : int n), (a `>> 0) = a.
Proof. move=> n [a Ha]. apply mk_int_pi. by rewrite bits.shrl_0. Qed.

Lemma shrl_Z2u_0 : forall n k, Z2u n 0 `>> k = Z2u n 0.
Proof. move=> n k. apply mk_int_pi => /=. by rewrite bits.adjust_u_nil bits.shrl_zeros. Qed.

Lemma shrl_Zpower : forall n k l, (k < n)%nat -> (l <= k)%nat -> Z2u n (2 ^^ k) `>> l = Z2u n (2 ^^ (k - l)).
Proof.
move=> n k l Hkn Hlk.
apply mk_int_pi => /=.
rewrite !bitZ.Z2u_2_Zpower /bits.adjust_u /= !size_nseq.
have [X|X] : (k.+1 < n \/ k.+1 < n = false)%nat by destruct (k.+1 < n)%nat; auto.
- rewrite X.
  move/leP : Hkn => Hkn.
  move/leP : X => X.
  have [Y|Y] : ((k - l).+1 < n \/ (k - l).+1 < n = false)%nat by destruct ((k - l).+1 < n)%nat; auto.
  + rewrite Y.
    move/ltP : Y => Y.
    rewrite /bits.zext (_ : bits.zeros k = bits.zeros (k - l) ++ bits.zeros l); last first.
      rewrite bits.zeros_app.
      f_equal.
      rewrite -minusE -plusE; move/leP in Hlk; omega.
    rewrite -cat1s 2!catA (bits.shrl_app_zeros l (n - l)); last first.
      rewrite !size_cat /= !size_nseq.
      rewrite addnBA // addn1 -subSn //; last first.
        by move/leP : Hkn.
      rewrite addnC subSS subnKC //.
      by move/leP in Hkn; rewrite ltnW.
    rewrite !catA bits.zeros_app.
    rewrite -catA.
    f_equal.
    f_equal.
    rewrite addnC -subSn // subnBA; last first.
      by move/leP in Hkn; rewrite ltnW.
    rewrite addnC addnBA //.
    by rewrite addnC.
    by move/leP in Hkn.
  + rewrite Y.
    move/ltP : Y.
    move/not_gt => Y.
    rewrite /bits.zext (_ : bits.zeros k = bits.zeros (k - l) ++ bits.zeros l); last first.
      rewrite bits.zeros_app.
      f_equal.
      rewrite -minusE -plusE; move/leP in Hlk; omega.
    rewrite -cat1s 2!catA (bits.shrl_app_zeros l (n - l)); last first.
      rewrite !size_cat /= !size_nseq.
      rewrite addnBA // addn1 -subSn //; last first.
        by move/leP : Hkn.
      rewrite addnC subSS subnKC //.
      by move/leP in Hkn; rewrite ltnW.
    have Z : ((k - l).+1 - n)%nat = O by rewrite -!minusE; omega.
    rewrite Z /= !catA bits.zeros_app.
    suff : (l + (n - k.+1))%nat = O by move => ->.
    rewrite -!minusE -plusE.
    rewrite -!minusE in Z Y; omega.
- rewrite X.
  move/leP in X.
  apply not_lt in X.
  have Y : k = (n - 1)%coq_nat by move/ltP in Hkn; omega.
  rewrite minusE in Y.
  rewrite Y /= (_ : (n-1).+1 - n = O)%nat; last first.
    rewrite -!minusE in Y *; move/ltP in Hkn; omega.
  rewrite /=.
  destruct n => //.
  inversion Hkn.
  rewrite subSS subn0 in Y; subst k.
  clear Hkn X.
  destruct l.
    by rewrite subn0 subSS subn0 ltnn subnn.
  have -> : ((n.+1 - 1 - l.+1).+1 < n.+1)%nat = true.
    rewrite subSS subn0 subnS ltnS prednK //; last by ssromega.
    by rewrite leq_subr.
  rewrite /bits.zext.
  rewrite (_ : n.+1 - 1 = n)%nat; last by rewrite subn1.
  have -> : bits.zeros n = bits.zeros (n - l.+1) ++ bits.zeros l.+1.
    by rewrite bits.zeros_app subnK.
  rewrite -cat1s catA (bits.shrl_app_zeros _ (n - l)); last by rewrite /= size_nseq -subSn.
  do 2 f_equal.
  rewrite -subSn // subnBA //; last by ssromega.
  by rewrite addnC addnK.
Qed.

Lemma shrl_overflow : forall n (a : int n) k, u2Z a < 2 ^^ k -> a `>> k = Z2u n 0.
Proof.
move=> n [a Ha] k H.
case: (le_lt_dec n k) => [|/ltP]X.
- apply mk_int_pi => /=.
  rewrite (bits.shrl_overflow n) //; last by apply/leP.
  by rewrite bits.adjust_u_nil.
- rewrite /le_n /= in H.
  apply mk_int_pi.
  rewrite bits.adjust_u_nil [int_lst _]/=.
  apply bitZ.ult_shrl_overflow => //.
  rewrite (_ : 2 ^^ k = bitZ.u2Z (bits.zeros (n - k.+1) ++ true :: bits.zeros k) ) in H; last first.
    by rewrite bitZ.u2Z_app bits.zeros_app bitZ.u2Z_zeros /= bitZ.u2Z_zeros size_nseq addZ0.
  apply (bitZ.ult_correct' n) in H => //.
  rewrite (bits.adjust_u_S'' n k.+1 (bitZ.Z2u (2 ^^ k))) //.
  by rewrite bitZ.Z2u_2_Zpower.
  by rewrite bitZ.Z2u_2_Zpower /= size_nseq.
  by rewrite size_cat /= !size_nseq addnC subnKC.
Qed.

Lemma shl_shrl : forall n (a : int n) m, u2Z a < 2 ^^ m -> (a `<< (n - m)) `>> (n - m) = a.
Proof. move=> n [l Hn] m /= H. apply mk_int_pi => /=. by apply bitZ.shrl_lst_shl. Qed.

Lemma shrl_shl : forall n (a : int n) m, a `% m = Z2u m 0 -> (a `>> m) `<< m = a.
Proof.
move=> n [a Ha] m //= [H].
apply mk_int_pi => /=.
rewrite bits.adjust_u_nil in H.
case/boolP : (m <= n)%nat => X.
- rewrite (bits.shl_shrl n) //.
  rewrite -H /bits.adjust_u Ha.
  have -> : (n < m = false)%nat by move/leP in X; apply/ltP; omega.
  by rewrite cat_take_drop.
- rewrite (bits.shrl_overflow n) //; last by rewrite -ltnNge in X; rewrite ltnW.
  rewrite bits.shl_zeros.
  rewrite /bits.adjust_u Ha in H.
  move: H.
  rewrite -ltnNge in X.
  rewrite X /bits.zext (bits.zeros_app2 m (m - n)); last by apply/leP; rewrite leq_subr.
  rewrite subnBA; last by rewrite ltnW.
  move/eqP.
  rewrite eqseq_cat; last by rewrite size_nseq.
  case/andP => _ /eqP ->.
  by rewrite addnC addnK.
Qed.

Lemma shrl_rem : forall n (a : int n) k k' (kk' : (n = k + k')%nat),
  zext k ((a `>> k ) `% k') = @eq_rect _ _ _ (a `>> k) _ kk'.
Proof.
move=> n [a Ha] /= k k' kk'.
symmetry.
apply mk_int_pi'.
rewrite /= /bits.zext (bits.shrl_tail n) //; last by rewrite kk'; ssromega.
f_equal.
rewrite /bits.adjust_u size_cat size_nseq.
rewrite size_take kk' addnC addnK Ha kk'.
case: (boolP (k == O)) => k0.
  by rewrite (eqP k0) add0n add0n ltnn ltnn subnn drop0.
have H1 : (k' < k + k')%nat.
  destruct k as [|k] => //.
  by rewrite addSn ltnS leq_addl.
rewrite H1.
by rewrite ltnNge ltnW //= addnK drop_size_cat // size_nseq.
Qed.

Definition shra m n (a : int n) : int n := mk_int (bits.size_shra n m (int_lst a) (int_prf a)).

Definition shr_shrink m n (a : int n) : int (n - m)%nat :=
  mk_int (bits.size_shr_shrink n m (int_lst a) (int_prf a)).

Lemma shr_shrink_overflow : forall n (a : int n) k, (k >= n)%nat ->
  shr_shrink k a = Z2u (n - k)%nat 0.
Proof.
move=> n [a Ha] k Hn.
rewrite /shr_shrink /= /Z2u.
apply: mk_int_pi.
rewrite -subn_eq0 in Hn.
move/eqP in Hn.
rewrite bits.shr_shrink_overflow.
- by rewrite Hn bits.adjust_u_0.
- rewrite Ha -subn_eq0; by apply/eqP.
Qed.

Definition int_and n (a b : int n) : int n :=
  mk_int (bits.size_and n (int_lst a) (int_lst b) (int_prf a) (int_prf b)).
Notation "a '`&' b" := (int_and a b) : machine_int_scope.

Lemma int_and_0 : forall n a, a `& Z2u n 0 = Z2u n 0.
Proof.
move=> n [j H].
rewrite /int_and /=.
apply: mk_int_pi.
by rewrite (bits.adjust_u_nil n) bits.andl0.
Qed.

Lemma int_andC : forall n (a b : int n), a `& b = b `& a.
Proof. move=> n [a Ha] [b Hb] /=. apply: mk_int_pi => /=. by rewrite (bits.andC n). Qed.

Lemma int_and_idempotent : forall n (a : int n), a `& a = a.
Proof. move=> n [a Ha]; apply mk_int_pi => /=. by apply (bits.and_idempotent n). Qed.

Lemma int_even_and_1 : forall n (a : int n), Zeven (u2Z a) -> a `& Z2u n 1 = Z2u n 0.
Proof.
move=> n [a Ha] /= H.
apply: mk_int_pi => /=.
rewrite bits.adjust_u_nil // /bits.adjust_u /=.
have [X|X] : (1 < n)%nat \/ (1 < n)%nat = false by case (1 < n)%nat; auto.
- rewrite X /bits.zext.
  destruct n => //.
  destruct n => //.
  case/lastP : a => // hda tla in Ha H *.
  move: Ha; rewrite size_rcons; case => Ha.
  destruct tla => //.
  + move: (bitZ.Zodd_lst_true hda) => Hnot.
    rewrite -cats1 in H.
    by apply Zeven_not_Zodd in H.
  + rewrite -cats1 (bits.and_app n.+1) /= /bits.bit_and //=.
      by rewrite (_ : false :: bits.zeros n = bits.zeros n.+1) // bits.andl0 // -nseqS.
    by rewrite size_nseq.
- rewrite X.
  destruct n => //.
  destruct a => //.
  destruct n => //.
  destruct a => //.
  destruct a => //.
  by destruct b.
Qed.

Lemma int_odd_and_1 : forall n (a : int n), Zodd (u2Z a) -> a `& Z2u n 1 = Z2u n 1.
Proof.
move=> n [a Ha] /= H.
apply: mk_int_pi => /=.
rewrite /bits.adjust_u /=.
case/boolP : (1 < n)%nat => X.
- rewrite /bits.zext.
  destruct n => //.
  case/lastP : a => // hda tla in Ha H *.
  move: Ha; rewrite size_rcons; case => Ha.
  destruct tla => //.
  + rewrite -cats1 subSS subn0 (bits.and_app n) /= /bits.bit_and //=.
      by rewrite bits.andl0.
    by rewrite size_nseq.
  + move: (bitZ.Zeven_ulst_false hda).
    by rewrite cats1 => /Zeven_not_Zodd.
- destruct n => //.
  destruct a => //.
  destruct n => //.
  destruct a => //.
  destruct a => //.
  by destruct b.
Qed.

Lemma int_and_rem_1 : forall n (a : int n), u2Z (a `& Z2u n 1) = u2Z (a `% 1).
Proof.
move=> [|n] [a Ha] /=.
- rewrite /bits.adjust_u Ha /=.
  by destruct a.
- move: a n Ha.
  elim/last_ind => //.
  move=> hd tl _ n H.
  rewrite size_rcons in H.
  case: H => H.
  rewrite (bits.adjust_u_S'' n.+1 1 (true :: nil)) //= subSS subn0 -cats1 (bits.and_app n) //.
  rewrite bits.andl0 //.
  rewrite bitZ.u2Z_app bits.zeros_app bitZ.u2Z_zeros.
  rewrite (bits.adjust_u_S O hd tl n.+1) //; last by rewrite size_cat addn1 H.
  rewrite bits.adjust_u_0 /=.
  by destruct tl.
  by rewrite size_nseq.
Qed.

Lemma rem_and : forall n (a : int n) k (Hkn : (k <= n)%nat),
  cast_subnK Hkn (zext (n - k)%nat (a `% k)) = (a `& Z2u n (2 ^^ k - 1)).
Proof.
move=> n [a Ha] k Hkn.
rewrite /cast_subnK /cast.
apply: mk_int_pi' => /=.
rewrite bitZ.Z2u_2_Zpower_m1 /bits.adjust_u Ha size_nseq.
have -> : (n < k)%nat = false by apply/negbTE; rewrite -leqNgt.
rewrite leq_eqVlt in Hkn.
case/orP : Hkn => X.
- move/eqP in X; subst k.
  by rewrite ltnn subnn /= /bits.zext /= !drop0 bits.andl1.
- rewrite X /bits.zext -(cat_take_drop (n - k)%nat a) (bits.and_app (n - k)); last 2 first.
    by rewrite size_takel // Ha leq_subr.
    by rewrite size_nseq.
  rewrite bits.andl0; last by rewrite size_takel // -Ha leq_subr.
  rewrite bits.andl1; last first.
    rewrite size_drop Ha subnBA; last by rewrite ltnW.
    by rewrite addnC addnK.
  by rewrite drop_size_cat // size_takel // Ha leq_subr.
Qed.

Definition int_or n (a b : int n) : int n :=
  mk_int (bits.size_or n (int_lst a) (int_lst b) (int_prf a) (int_prf b)).
Notation "a '`|`' b" := (int_or a b) : machine_int_scope.

Lemma int_or_0 n : forall (v : int n), v `|` Z2u n 0 = v.
Proof. case=> v Hv; apply mk_int_pi => /=; by rewrite (bits.adjust_u_nil n) bits.orl0. Qed.

Lemma int_orC : forall n (a b : int n), a `|` b = b `|` a.
Proof. move=> n [a Ha] [b Hb]. apply mk_int_pi. by rewrite (bits.orC n). Qed.

Lemma int_or_idempotent : forall n (a : int n), a `|` a = a.
Proof. move=> n [a Ha]; apply mk_int_pi => /=. by apply (bits.or_idempotent n). Qed.

Lemma bits_int_or : forall n (a b : int n), bits (a `|` b) = bits.or (bits a) (bits b).
Proof.
move=> n [a Ha] [b Hb].
by rewrite /bits /= (bits.orC n) // (bits.rev_or n) // (bits.orC n) // size_rev.
Qed.

Lemma shl_distr_or : forall n (a b : int n) m, (a `|` b) `<< m = (a `<< m) `|` (b `<< m).
Proof.
move=> n [a Ha] [b Hb] m; apply mk_int_pi => /=.
by eapply bits.shr_or; eauto.
Qed.

Lemma shrl_distr_or : forall n (a b : int n) m, (a `|` b) `>> m = (a `>> m) `|` (b `>> m).
Proof.
move=> n [a Ha] [b Hb] m; apply mk_int_pi => /=.
by eapply bits.shrl_or; eauto.
Qed.

Lemma rem_distr_or : forall n (a b : int n) m, (a `|` b) `% m = (a `% m) `|` (b `% m).
Proof.
move=> n [a Ha] [b Hb] m /=; apply mk_int_pi => /=.
by apply (bits.adjust_u_or n).
Qed.

Lemma or_sh_rem : forall n (a : int n) k (H : (k <= n)%nat),
  a = ((a `>> k) `<< k) `|` (cast_subnK H (zext (n - k) (a `% k))).
Proof.
move=> n [a Ha] k Hkn /=.
apply mk_int_pi => /=.
rewrite (bits.shl_shrl n) //.
rewrite mk_int_pi'' /= /zext /bits.zext.
rewrite (bits.or_cat (n - k) k); last 4 first.
  rewrite size_take Ha.
  case: ifP => // /negbT; rewrite -leqNgt. rewrite -!minusE => /leP; move/leP in Hkn =>?; omega.
  by apply size_nseq.
  by apply size_nseq.
  by apply bits.size_adjust_u.
rewrite bits.orl0; last first.
  rewrite size_take Ha.
  case: ifP => // /negbT; rewrite -leqNgt. rewrite -!minusE => /leP; move/leP in Hkn =>?; omega.
rewrite (bits.orC k) //; last 2 first.
  by apply size_nseq.
  by apply bits.size_adjust_u.
rewrite bits.orl0; last by apply bits.size_adjust_u.
rewrite /bits.adjust_u Ha.
have -> : (n < k = false)%nat by apply/negbTE; rewrite -leqNgt.
by rewrite cat_take_drop.
Qed.

Definition int_xor n (a b : int n) : int n :=
  mk_int (bits.size_xor n (int_lst a) (int_lst b) (int_prf a) (int_prf b)).
Notation "a '`(+)' b" := (int_xor a b) : machine_int_scope.

Lemma int_xor_0: forall n (v : int n), v `(+) Z2u n 0 = v.
Proof.
move=> n [lst e]; rewrite /int_xor /=.
apply: mk_int_pi.
by rewrite (bits.adjust_u_nil n) bits.xorl0.
Qed.

Lemma int_xorC : forall n (a b : int n), a `(+) b = b `(+) a.
Proof. move=> n [a Ha] [b Hb]. apply: mk_int_pi => /=. by eapply bits.xorC; eauto. Qed.

Lemma int_xorA : forall n (a b c : int n), (a `(+) b) `(+) c = a `(+) (b `(+) c).
Proof. move=> n [a Ha] [b Hb] [c Hc]. apply: mk_int_pi => /=. symmetry. by eapply bits.xorA; eauto. Qed.

Lemma int_xor_self : forall n (a : int n), a `(+) a = `( 0 )_ n.
Proof. move=> n [a Ha]. apply: mk_int_pi => /=. rewrite bits.adjust_u_nil. by apply bits.xor_self. Qed.

Lemma size_cplt1' n a : size a = n -> size (bits.cplt1 a) = n.
Proof. move=> H; by rewrite bits.size_cplt1. Qed.

Definition int_not n (a : int n) : int n := mk_int (@size_cplt1' n (int_lst a) (int_prf a)).

Lemma int_and_1s : forall n a, a `& int_not (Z2u n 0) = a.
Proof.
move=> n [j H].
rewrite /int_and /=.
apply: mk_int_pi.
by rewrite (bits.adjust_u_nil n) bits.cplt1_zeros bits.andl1.
Qed.

Lemma int_not_or n : forall (a b : int n), int_not (a `|` b) = int_not a `& int_not b.
Proof.
move=> [a Ha] [b Hb]; apply mk_int_pi => /=; by apply (bits.cplt1_or n).
Qed.

Lemma int_xor_1s n : forall (a : int n), a `(+) int_not (Z2u n 0) = int_not a.
Proof.
case=> a Ha.
apply mk_int_pi => /=.
rewrite bits.adjust_u_nil bits.cplt1_zeros; by apply bits.xor_ones.
Qed.

(* NB: Lemma int_and_rem : forall n (a : int n) k,
  a `& z_extend (n-k) (int_not (Z2u k 0)) = a `% k. does not type*)

(* NB: Lemma int_and_rem : forall n (a : int n),
  a `& Z2u n 1 = a `% 1. does not type*)

Definition cplt2 n (a : int n) : int n.
apply mk_int with (bits.cplt2 (int_lst a)).
rewrite bits.size_cplt2.
by destruct a.
Defined.
(* := mk_int (bits.size_cplt2 _ n (int_lst a) (int_prf a)).*)

Lemma cplt2_zero n : cplt2 (Z2u n 0) = Z2u n 0.
Proof.
rewrite /cplt2.
apply mk_int_pi => /=.
by rewrite bits.adjust_u_nil bits.cplt2_zeros.
Qed.

Lemma cplt2_1s n : cplt2 (int_not (Z2u n 0)) = Z2u n 1.
Proof.
rewrite /cplt2.
apply mk_int_pi => /=.
by rewrite bits.adjust_u_nil bits.cplt1_zeros bits.cplt2_ones.
Qed.

Lemma not_add_1_cplt2: forall n (v : int n), (n > 1)%nat ->
  int_not v `+ Z2u n 1 = cplt2 v.
Proof.
move=> n [lst e] Hn.
rewrite /add /cplt2 /=.
apply mk_int_pi.
rewrite /bits.cplt2 bits.zext_true /bits.adjust_u /=.
destruct n.
- by inversion Hn.
- destruct n.
  + by rewrite ltnn in Hn.
  + by rewrite /= /bits.zext e.
Qed.

Lemma cplt2_inj {n} : forall (a b : int n), cplt2 a = cplt2 b -> a = b.
Proof.
move=> [a Ha] [b Hb].
rewrite /cplt2 /=.
case.
destruct n.
  destruct a => //.
  destruct b => // _.
  by apply mk_int_pi.
move/(@bits.cplt2_inj _ _ _ Ha Hb) => ?; subst a.
by apply mk_int_pi.
Qed.

Lemma sub_cplt2 : forall n (a b : int n.+1), a `- b = a `+ cplt2 b.
Proof.
move=> n [a Ha] [b Hb].
apply mk_int_pi => /=.
rewrite (bits.sub_add_cplt1 n.+1) //.
rewrite /bits.cplt2.
rewrite -(bits.addA n.+1) //; last 2 first.
  by rewrite bits.size_cplt1.
  by rewrite (bits.size_zext 1) // Hb subnK.
rewrite -(bits.carry_add _ _ (bits.zeros n.+1)); last 2 first.
  rewrite (bits.size_add n.+1) //; last by rewrite bits.size_cplt1.
  by rewrite Hb -addn1 subnK.
  by rewrite (bits.size_add n.+1) // bits.size_cplt1.
rewrite (bits.addA n.+1) //; last 2 first.
  by rewrite bits.size_cplt1.
  by rewrite size_nseq.
by rewrite bits.addl0 // bits.size_cplt1 Hb.
Qed.

Definition concat_size n m : int (n + m) -> int (m + n).
Proof. move=>  [nm Hnm]; exists nm; by rewrite addnC. Defined.

Definition concat n m (a : int n) (b : int m) : int (n + m) :=
  add (concat_size (shl_ext m a)) (zext n b).
Notation "a `|| b " := (concat a b) (at level 68, left associativity, format "'[' a  `||  b ']'") : machine_int_scope.

Program Definition concatE_def := forall n m (a : int n) (b : int m),
  a `|| b = @mk_int _ (int_lst a ++ int_lst b) _.
Next Obligation.
destruct a. destruct b.
by rewrite size_cat /= e e0.
Defined.

Lemma concatE : concatE_def.
Proof.
red.
move=> n m [a Ha] [b Hb] /=.
apply mk_int_pi => /=.
by rewrite /bits.shl_ext /bits.zext bits.addC bits.add_app.
Qed.

Lemma zext_concat : forall n (a : int n) m, zext m a = `( 0 )_ m `|| a.
Proof.
move=> n [a Ha] /= m.
rewrite concatE.
rewrite /zext /= /concat /=.
apply mk_int_pi => /=.
by rewrite /bits.zext bits.adjust_u_nil.
Qed.

Lemma concatA : forall k m n (a : int k) (b : int m) (c : int n),
  a `|| b `|| c = castA (@addnA _ _ _) (a `|| (b `|| c)).
Proof.
move=> k m n a b c.
rewrite !concatE.
apply mk_int_pi => /=.
by rewrite catA.
Qed.

Lemma or_concat n : forall (a : int n) (b : int n) k (Hkn: (k <= n)%nat),
  u2Z a < 2 ^^ k ->
  b `% k = Z2u k 0 ->
  (b `|` a) = cast_subnK Hkn (shr_shrink k b `|| (a `% k)).
Proof.
move=> [a Ha] [b Hb] k Hkn Hu2Za [Hbk].
rewrite bits.adjust_u_nil in Hbk.
symmetry.
apply mk_int_pi' => /=.
rewrite /bits.shl_ext /bits.zext.
rewrite bits.addC bits.add_app; last 2 first.
  by rewrite (bits.size_shr_shrink n).
  by rewrite bits.size_adjust_u.
rewrite -{2}(bits.shr_shrink_adjust_u _ _ _ Hb Hkn) Hbk.
rewrite -{2}(bits.shr_shrink_adjust_u _ _ _ Ha Hkn).
rewrite (bits.or_cat (n - k) k); last 4 first.
  by rewrite (bits.size_shr_shrink n).
  by rewrite size_nseq.
  by rewrite (bits.size_shr_shrink n).
  by rewrite bits.size_adjust_u.
congr cat.
- rewrite /= in Hu2Za.
  apply (bitZ.u2Z_power_inv n) in Hu2Za => //.
  case: Hu2Za => a' Hu2Za.
  rewrite Hu2Za bits.shr_shrink_app //.
  by rewrite bits.orl0 // (bits.size_shr_shrink n).
  rewrite Hu2Za size_cat addnC /= size_nseq -minusE -plusE in Ha.
  move/leP in Hkn.
  omega.
- rewrite (bits.orC k) //; last 2 first.
    by rewrite size_nseq.
    by rewrite bits.size_adjust_u.
  by rewrite bits.orl0 // bits.size_adjust_u.
Qed.

Lemma rem_concat n : forall (a : int n) m (b : int m), (a `|| b) `% m = b.
Proof.
move=> [l e] m [l0 e0] /=.
apply mk_int_pi.
rewrite /bits.adjust_u (bits.size_add (n + m)); last 2 first.
  by rewrite (bits.size_shl_ext _ _ m e) addnC.
  by rewrite (bits.size_zext _ _ n e0).
have -> : (n + m < m = false)%nat by apply/negbTE; rewrite -leqNgt leq_addl.
by rewrite /bits.zext /bits.shl_ext bits.addC bits.add_app // addnK drop_size_cat.
Qed.

Lemma concat_shl : forall n (a : int n) m,
  a `|| Z2u m 0 = castC (@addnC _ _) (zext m a `<< m).
Proof.
move=> n [a Ha] m.
apply mk_int_pi => /=.
rewrite bits.adjust_u_nil.
rewrite /bits.zext bits.zeros_app bits.addl0.
by rewrite /bits.shl_ext bits.shl_zeros_cat.
by rewrite (@bits.size_shl_ext n) // addnC.
Qed.

(** interpretation of int as unsigned integers and related properties *)

(** correctness of the addition w.r.t. unsigned integers *)
Lemma u2Z_add n : forall (a b : int n), u2Z a + u2Z b < 2 ^^ n ->
  u2Z (a `+ b) = u2Z a + u2Z b.
Proof. move=> [a Ha] [b Hb] /= H; by rewrite (bitZ.add_nat n). Qed.

Lemma u2Z_add_overflow : forall n (a b : int n), 2 ^^ n <= u2Z a + u2Z b ->
  u2Z (a `+ b) + 2 ^^ n = u2Z a + u2Z b.
Proof. move=> n [a Ha] [b Hb] /= H; by rewrite bitZ.add_overflow. Qed.

(** correctness of subtraction w.r.t. unsigned integers *)
Lemma u2Z_sub : forall n (a b : int n), u2Z a >= u2Z b -> u2Z (sub a b) = u2Z a - u2Z b.
Proof.
move=> n [a Ha] [b Hb] /= H.
destruct n.
- destruct a => //; by destruct b.
- move: (bitZ.sub_nat _ _ _ false Ha Hb isT) => /= X; omega.
Qed.

Lemma u2Z_sub_overflow : forall n (a b : int n), u2Z a < u2Z b ->
  u2Z (sub a b) = u2Z a + 2 ^^ n - u2Z b.
Proof.
move=> n [a Ha] [b Hb] /= H.
destruct n.
- destruct a => //; by destruct b.
- move: (bitZ.sub_nat_overflow _ _ _ false Ha Hb isT) => X.
  rewrite [expZ]lock /= -lock in X; omega.
Qed.

(** correctness of the unsigned multiplication (with truncation) *)
Lemma u2Z_mul : forall n (a b : int n), u2Z a * u2Z b < 2 ^^ n ->
  u2Z (mul a b) = u2Z a * u2Z b.
Proof. move=> n [a Ha] [b Hb] H; by rewrite /u2Z /mul bitZ.mul_nat. Qed.

(** correctness of the unsigned multiplication *)
Lemma u2Z_umul: forall n (a b : int n), u2Z (umul a b) = u2Z a * u2Z b.
Proof.
move=> n [a Ha] [b Hb] /=.
destruct n.
destruct a => //; destruct b => //=.
by rewrite (bitZ.umul_nat n).
Qed.

Lemma u2Z_shl : forall n L (x : int L) l, (n + l <= L)%nat -> u2Z x < 2 ^^ l ->
  u2Z (shl n x) = u2Z x * 2 ^^ n.
Proof.
move=> n L [x Hx] l H1 H2.
rewrite /u2Z /shl /=.
eapply (bitZ.shl_u2Z n).
by apply Hx.
by apply H1.
by apply H2.
Qed.

Lemma u2Z_shl' : forall l (x : int l), forall L, u2Z x < 2 ^^ L -> forall n, (n + L <= l)%nat ->
  u2Z (shl n x) <= 2 ^^ (L + n) - 2 ^^ n.
Proof. move=> l [x Hx] L HL n Hn /=. by apply bitZ.shl_u2Z' with l. Qed.

Lemma u2Z_shl_overflow : forall n l (x : int l), (n >= l)%nat -> u2Z (shl n x) = 0.
Proof. move=> n l [x Hx] Hn /=. move/leP in Hn; by rewrite (bits.shl_overflow n l) // bitZ.u2Z_zeros. Qed.

Lemma cast_shl n k (a : int k) (Hkn : (k <= n)%nat) m (kmn : (k + m <= n)%nat) :
  cast_subnK Hkn (zext (n - k) a `<< m) = (cast_subnK Hkn (zext (n - k) a )) `<< m.
Proof.
apply u2Z_inj.
rewrite u2Z_cast.
symmetry.
have mn : (m <= n)%nat by rewrite -(leq_add2l k) (leq_trans kmn) // leq_addl.
rewrite (@u2Z_shl _ _ _ (n - m)); last 2 first.
  by rewrite subnKC.
  rewrite u2Z_cast u2Z_zext.
  apply: ltZ_leZ_trans; first exact: max_u2Z.
  by apply/leZP; rewrite Zpower_2_le -(leq_add2r m) subnK.
rewrite u2Z_cast (@u2Z_shl _ _ _ (n - m)) //.
  by rewrite subnK // subnKC.
rewrite u2Z_zext.
apply: ltZ_leZ_trans; first exact: max_u2Z.
apply/leZP; by rewrite Zpower_2_le -(leq_add2r m) subnK.
Qed.

Lemma u2Z_shl_Zmod : forall l (a : int l) k, (k < l)%nat ->
  u2Z (shl k a) = (u2Z a * 2 ^^ k) mod 2 ^^ l.
Proof. move=> l [a Ha] k Hkl /=. by apply bitZ.shl_u2Z_overflow. Qed.

Lemma u2Z_shl_rem : forall n (a : int n) k, u2Z (a `<< k) = 2 ^^ k * u2Z (a `% (n - k)).
Proof.
move=> n [a Ha] /= k.
have [X|X] : (k <= n \/ k > n)%coq_nat by omega.
- rewrite -{1}(cat_take_drop k a).
  rewrite bits.shl_cat //; last first.
    rewrite size_takel // Ha; by apply/leP.
  rewrite bitZ.u2Z_app_zeros /bits.adjust_u.
  have -> : (size a < n - k)%nat = false by rewrite Ha -minusE; apply/ltP; omega.
  rewrite -{3}(cat_take_drop k a).
  rewrite drop_size_cat; first by rewrite mulZC.
  rewrite size_takel Ha; last by apply/leP.
  rewrite subnBA; last by apply/leP.
  by rewrite addnC addnK.
- rewrite (bits.shl_overflow _ n) //; last by omega.
  have -> : (n - k = O)%nat by rewrite -minusE; omega.
  by rewrite bits.adjust_u_0 /= bitZ.u2Z_zeros mulZ0.
Qed.

Lemma u2Z_shl_ext : forall n l (x : int l), u2Z (shl_ext n x) = u2Z x * 2 ^^ n.
Proof. move=> n l [x Hx] //=. by apply bitZ.shl_ext_u2Z with (size x). Qed.

Lemma u2Z_shl_ext' : forall l (x : int l), forall k, u2Z x < 2 ^^ k -> forall n,
  u2Z (shl_ext n x) <= 2 ^^ (k + n) - 2 ^^ n.
Proof. move=> l [x Hx] k H n //=. by apply bitZ.shl_ext_u2Z' with l. Qed.

Lemma u2Z_shl_ext'' : forall l (x : int l), forall k, u2Z x < 2 ^^ k -> forall n,
  u2Z (shl_ext n x) + 2 ^^ n <= 2 ^^ (k + n).
Proof. move=> l x k Hx n. move: (@u2Z_shl_ext' _ _ _ Hx n) => H; omega. Qed.

Lemma Zle_u2Z_shr_shrink : forall n (a : int n) k, u2Z (shr_shrink k a) * 2 ^^ k <= u2Z a.
Proof.
move=> n [a Ha] k /=.
move: a Ha k.
induction n.
- move=> [|hd tl] // Ha k.
  by rewrite bits.shr_shrink_nil.
- move=> a Ha k.
  case/lastP : a => // tla hda H in Ha *.
  rewrite size_rcons in H.
  case: H => H.
  destruct k.
  + simpl; omega.
  + rewrite -cats1 bits.shr_shrink_S ZpowerS bitZ.u2Z_last.
    move: (IHn _ H k) => IHn0.
    have -> : bitZ.u2Z (bits.shr_shrink k tla) * (2 * 2 ^^ k) =
        2 * (bitZ.u2Z (bits.shr_shrink k tla) * 2 ^^ k) by ring.
    destruct hda; simpl bitZ.u2Z; omega.
Qed.

Lemma u2Z_shr_shrink : forall l (x : int l) n, (l >= n)%nat ->
  u2Z (shr_shrink n x) * 2^^n + u2Z (x `% n) = u2Z x.
Proof.
move=> l [x Hx] n Hn /=.
rewrite -bitZ.u2Z_app_zeros {2}(_ : n = size (bits.adjust_u x n)); last by rewrite bits.size_adjust_u.
rewrite -bitZ.u2Z_app (bits.shr_shrink_adjust_u (size x)) //.
by rewrite Hx.
Qed.

Lemma u2Z_shr_shrink' : forall l (x : int l) (n : nat), (l >= n)%nat ->
  u2Z (shr_shrink n x) * 2^^n = u2Z x - u2Z (x `% n).
Proof. intros. generalize (u2Z_shr_shrink x H); intro. omega. Qed.

Lemma u2Z_shrl : forall l (x : int l) n, (l >= n)%nat ->
  u2Z (x `>> n) * 2^^n + u2Z (x `% n) = u2Z x.
Proof.
move=> l [x Hx] n Hnl /=.
rewrite -(bits.shr_shrink_shrl _ _ (refl_equal _) n).
rewrite bitZ.u2Z_app bits.zeros_app bitZ.u2Z_zeros /= -bitZ.u2Z_app_zeros {2}(_ : n = size (bits.adjust_u x n)).
by rewrite -bitZ.u2Z_app (bits.shr_shrink_adjust_u (size x)) // Hx.
by rewrite bits.size_adjust_u.
by rewrite Hx.
Qed.

Lemma shrl_lt : forall n (a : int n) m, u2Z (a `>> m) < 2 ^^ (n - m).
Proof.
move=> n [a Ha] m /=.
have [X|X] : (m <= n \/ n < m)%coq_nat by omega.
  rewrite (bits.shrl_tail n) // bitZ.u2Z_app bits.zeros_app bitZ.u2Z_zeros /=.
  apply bitZ.max_u2Z.
  rewrite size_take Ha.
  by case: ifP => // /negbT; rewrite ltnNge negbK.
rewrite (_ : n - m = O)%nat /=.
rewrite (bits.shrl_overflow n) //.
by rewrite bitZ.u2Z_zeros.
apply/leP; omega.
rewrite -minusE; omega.
Qed.

Lemma u2Z_or m n : forall (a : int m) (b : int n),
  u2Z ((a `|| Z2u n 0) `|` zext m b) = (u2Z a * 2 ^^ n + u2Z b)%Z.
Proof.
move=> [a Ha] [b Hb] /=.
rewrite bits.adjust_u_nil /bits.zext bits.zeros_app bits.addl0; last first.
  by rewrite (bits.size_shl_ext m) // addnC.
rewrite /bits.shl_ext (bits.or_cat m n) //; last 2 first.
  by rewrite size_nseq.
  by rewrite size_nseq.
rewrite bits.orl0 // (bits.orC n) //; last by rewrite size_nseq.
by rewrite bits.orl0 // bitZ.u2Z_app bitZ.u2Z_app_zeros Hb.
Qed.

Lemma u2Z_rem : forall n (x : int n) m, (n >= m)%nat ->
  u2Z (x `% m) = u2Z x - u2Z (shr_shrink m x) * 2 ^^ m.
Proof. intros. generalize (u2Z_shr_shrink x H); intro. omega. Qed.

Lemma u2Z_rem' : forall n (a : int n) k, u2Z a < 2 ^^ k -> u2Z (a `% k) = u2Z a.
Proof. move=> n [a Ha] k /= H. by rewrite bitZ.adjust_u2Z. Qed.

Lemma u2Z_rem''_ : forall n (a : int n) k a', 0 < a' -> k <> O -> u2Z a = 2 ^^ k * a' -> u2Z (a `% k) = 0.
Proof.
elim.
- move=> [] [] // * /=.
  by rewrite bits.adjust_u_nil bitZ.u2Z_zeros .
- move=> n IHn [a Ha] k a' Ha'_pos Hk_pos H.
  have X : (0 < size a)%nat by rewrite Ha.
  elim/last_ind : a => // tl hd _ in X Ha H *.
  clear X.
  destruct hd.
  + have H1 : Zeven (u2Z (mk_int Ha)).
      rewrite H. apply Zeven_mult_Zeven_l. destruct k => //. by apply Zeven_power.
    have H2 : Zodd (u2Z (mk_int Ha)).
      rewrite /= -cats1; by apply bitZ.Zodd_lst_true.
    by apply Zeven_not_Zodd in H1.
  + rewrite /=.
    destruct k.
    * by rewrite bits.adjust_u_0.
    * rewrite -cats1 (bits.adjust_u_S _ _ _ n.+1); last 2 first.
        - clear H; by rewrite -cats1 in Ha.
        - move: (max_u2Z (mk_int Ha)) => X.
          rewrite H in X.
          have /Zpower_2_inv ? : 2 ^^ k.+1 < 2 ^^ n.+1.
            apply (@leZ_ltZ_trans (2 ^^ k.+1 * a')) => //.
            rewrite -{1}(mulZ1 (2 ^^ k.+1)).
            apply leZ_wpmul2l; first exact: expZ_ge0.
            omega.
          by rewrite ltnS ltnW.
      rewrite bitZ.u2Z_app bitZ.u2Z_app_zeros /= addZ0.
      rewrite ZpowerS [Zmult]lock /= -lock in H.
      rewrite size_rcons in Ha.
      case: Ha => Ha.
      destruct k.
      - by rewrite bits.adjust_u_0.
      - move: (IHn (mk_int Ha) (k.+1) _ Ha'_pos).
        rewrite [expZ _ _]lock /= -lock => -> //.
        rewrite -cats1 bitZ.u2Z_app bitZ.u2Z_app_zeros [expZ _ _]/= in H.
        symmetry in H.
        rewrite -mulZA mulZC addZ0 in H.
        by apply eqZ_mul2r in H.
Qed.

Lemma rem_Z2u_0 n k : Z2u n 0 `% k = Z2u k 0.
Proof.
move=> /=.
apply: mk_int_pi.
rewrite bits.adjust_u_nil /bitZ.Z2u bits.adjust_u_nil.
exact: bits.adjust_u_zeros.
Qed.

Lemma u2Z_rem'' n (a : int n) k a' : u2Z a = 2 ^^ k.+1 * a' -> u2Z (a `% k.+1) = 0.
Proof.
move=> H.
destruct a'.
- rewrite mulZC /= in H.
  have -> : a = Z2u n 0 by rewrite -H Z2u_u2Z.
  rewrite rem_Z2u_0 Z2uK //.
  split => //; exact: expZ_gt0.
- by eapply u2Z_rem''_; eauto.
- move: (min_u2Z a) => H1.
  suff [//] : ~ (0 <= u2Z a).
  apply ltZNge.
  rewrite H mulZC.
  apply Zmult_neg; by [apply Zlt_neg_0 | apply expZ_gt0].
Qed.

Lemma u2Z_rem_zext : forall n (a : int n) k m, u2Z (zext k a `% m) = u2Z (a `% m).
Proof.
move=> l [lst e] k n /=.
rewrite /bits.zext /bits.adjust_u size_cat size_nseq e.
case/boolP : (k + l < n)%nat => H0.
- have -> : (l < n)%nat by rewrite (leq_trans _ H0) // ltnS leq_addl.
  rewrite /bits.zext catA bits.zeros_app ( _ : (n - (k + l) + k) = n - l)%nat //.
  ssromega.
- case/boolP : (l < n)%nat => H1.
  + rewrite /bits.zext.
    have H2 : (k = (k + l - n) + (n - l))%nat by ssromega.
    by rewrite {2}H2 -bits.zeros_app -catA drop_cat size_nseq ltnn subnn drop0.
  + rewrite (_ : (k + l - n = k + ( l - n )))%nat; last by ssromega.
    rewrite drop_cat size_nseq.
    case: ifP => [ | _]; last by rewrite addnC addnK.
    by rewrite -{2}(addn0 k) ltn_add2l ltn0.
Qed.

Lemma u2Z_concat n l : forall (a : int n) (b : int l), u2Z (a `|| b) = u2Z a * 2 ^^ l + u2Z b.
Proof.
move=> [a Ha] [b Hb] /=.
rewrite (bitZ.add_nat (n + l)); last 3 first.
- by rewrite (bits.size_shl_ext n) // addnC.
- by rewrite (bits.size_zext l).
- rewrite /bits.zext bitZ.u2Z_app bits.zeros_app bitZ.u2Z_zeros /=.
  have H0 : bitZ.u2Z a < 2 ^^ n by apply bitZ.max_u2Z; rewrite Ha.
  move: {H0}(bitZ.shl_ext_u2Z' _ _ Ha _ H0 l) => H1.
  have H2 : bitZ.u2Z b < 2 ^^ l by apply bitZ.max_u2Z; rewrite Hb.
  omega.
- by rewrite (bitZ.shl_ext_u2Z l n) // /bits.zext bitZ.u2Z_app bits.zeros_app bitZ.u2Z_zeros.
Qed.

Lemma lt_n2Zlt n : forall (a b : int n), a `< b -> u2Z a < u2Z b.
Proof. move=> [a_lst Ha] [b_lst Hb] /= H. exact: (bitZ.ult_correct n). Qed.

Lemma le_n2Zle n : forall (a b : int n), a `<= b -> u2Z a <= u2Z b.
Proof.
move=> [a_lst Ha] [b_lst Hb] /= H.
apply le_nE in H.
case: H => H.
  apply Zeq_le.
  by case: H => ->.
exact/ltZW/(bitZ.ult_correct n).
Qed.

Lemma Zlt2lt_n : forall n (a b : int n), u2Z a < u2Z b -> a `< b.
Proof. move=> n [a Ha] [b Hb] /= H. apply: bitZ.ult_correct' => /=; eauto. Qed.

Lemma Zle2le_n : forall n (a b:int n), u2Z a <= u2Z b -> a `<= b.
Proof.
move=> l a b.
case/leZ_eqVlt => H; rewrite /le_n; apply/orP.
- right.
  move/u2Z_inj : H => <-.
  by apply bits.listbit_eq_refl.
- left; by apply Zlt2lt_n.
Qed.

(** interpretation of int as relative integers and related properties *)
Definition s2Z l (a : int l) : Z := match a with mk_int lst _ => bitZ.s2Z lst end.
Definition s2Zc n (a : int n) : Z := match a with mk_int lst _ => bitZ.s2Z lst end.
Lemma s2ZE : forall n (a : int n), s2Z a = s2Zc a. Proof. done. Qed.

Lemma max_s2Z : forall l (a : int l), s2Z a < 2 ^^ l.-1.
Proof.
move=> l [a Ha] /=.
destruct l as [|l] => /=.
destruct a as [|hd tl] => //=.
by apply bitZ.max_s2Z.
Qed.

Lemma min_s2Z : forall n (a : int n.+1), - 2 ^^ n <= s2Z a.
Proof. move=> l [a Ha] /=. by apply bitZ.min_s2Z. Qed.

Lemma s2Z_zext : forall k n (a : int n), (0 < k)%nat -> s2Z (zext k a) = u2Z a.
Proof. move=> [|k] n [a Ha] Hk //=; by rewrite bitZ.u2Z_falses. Qed.
Arguments s2Z_zext _ [n] _ _.

Lemma s2Z_inj : forall l (v w : int l), s2Z v = s2Z w -> v = w.
Proof. move=> l [v Hv] [w Hw] /= H. apply mk_int_pi. by eapply bitZ.s2Z_inj; eauto. Qed.

Lemma s2Z_cast : forall (f : nat -> nat -> nat) (P : nat -> nat -> Type)
  (H : forall k n : nat, P k n -> f k n = n) k n (Hkn : P k n) a,
  s2Z (cast H Hkn a) = s2Z a.
Proof.
move=> f P H k n Hkn [a Ha] /=.
rewrite /cast /eq_rect.
move: (H k n Hkn).
move: Ha.
rewrite H // => Ha H0.
suff : H0 = refl_equal n by move=> ->.
by apply proof_irrelevance.
Qed.

Lemma s2Z_castA k m n : forall (a : int (k + (m + n))), s2Z (castA (@addnA _ _ _) a) = s2Z a.
Proof. by case. Qed.

Definition weird n (a : int n.+1) : Prop := int_lst a = true :: bits.zeros n.

Lemma weirdE : forall n (a : int n.+1), weird a <-> u2Z a = 2 ^^ n.
Proof.
move=> n [a Ha]; rewrite /weird /=; split => H.
  rewrite H /=.
  rewrite size_nseq.
  by rewrite bitZ.u2Z_zeros addZ0.
by apply bitZ.u2Z_Zpower_inv.
Qed.

Lemma weirdE2 : forall n (a : int n.+1), weird a <-> s2Z a = - 2 ^^ n.
Proof.
move=> n [a Ha]; rewrite /weird /=; split => H.
  rewrite H /= size_nseq.
  by rewrite bitZ.u2Z_zeros addZ0.
by apply bitZ.s2Z_Zpower_inv.
Qed.

Lemma s2Z_cplt2: forall n (v : int n.+1), ~ weird v -> s2Z (cplt2 v) = - (s2Z v).
Proof.
move=> n [a Ha].
rewrite /weird /= => H.
by apply (bitZ.cplt2_correct n _ Ha).
Qed.

Lemma sext_s2Z : forall l (v : int l) n, s2Z (sext n v) = s2Z v.
Proof. move=> l [v Hv] /= n; by apply bitZ.sext_s2Z. Qed.

Definition Z2s n (l : Z) : int n := mk_int (bits.size_adjust_s n (bitZ.Z2s l)).
Definition Z2sc n (l : Z) : int n := mk_int (bits.size_adjust_s n (bitZ.Z2s l)).
Notation "'`(' x ')s_' n" := (Z2s n x).
Notation "'`(' x ')sc_' n" := (Z2sc n x).

Lemma Z2sE : forall n z, `( z )s_n = `( z )sc_ n. Proof. by []. Qed.

Lemma Z2sK_not_weird : forall (z : Z) m, - 2 ^^ m < z < 2 ^^ m -> s2Z ( `( z )s_m.+1 ) = z.
Proof.
move=> [|p|p] m H /=.
- destruct m as [|[|m]] => //.
  by rewrite /bits.adjust_s /= bits.sext_0 /= /bits.zeros -nseqS -/(bits.zeros _) bitZ.u2Z_zeros.
- rewrite /bits.adjust_s.
  destruct m as [|m].
  + case: H => /=; by case: p.
  + rewrite /= size_rev.
    move: (bitZ.pos2lst_len _ _ (proj2 H)); rewrite leq_eqVlt; case/orP => [/eqP ->|]; last first.
    * rewrite -ltnS => ->.
      rewrite bits.sext_0 /= bitZ.u2Z_app bitZ.u2Z_app_zeros bitZ.u2Z_zeros /=.
      by rewrite bitZ.u2Z_rev_poslst.
    * by rewrite ltnn subnn /= bitZ.u2Z_rev_poslst.
- rewrite /bits.adjust_s.
  destruct m as [|m].
  + case: H => /=; by case: p.
  + rewrite bits.size_cplt2 /= size_rev.
    have : (size (bitZ.pos2lst p) <= S m)%nat.
      apply bitZ.pos2lst_len; rewrite -(Zopp_neg p); omega.
    rewrite leq_eqVlt; case/orP => [/eqP size_p |]; last first.
    + rewrite -ltnS => ->.
      rewrite bitZ.sext_s2Z (bitZ.cplt2_correct (size (rev (bitZ.pos2lst p)))) //.
      by rewrite bitZ.s2Z_false bitZ.u2Z_rev_poslst -(Zopp_neg p) oppZK.
    + rewrite size_p ltnn subnn //= drop0 (bitZ.cplt2_correct m.+1) //; last first.
        by rewrite /= size_rev size_p.
      by rewrite bitZ.s2Z_false bitZ.u2Z_rev_poslst -(Zopp_neg p) oppZK.
Qed.

Lemma Z2sK_weird : forall z m, z = - 2^^m -> s2Z (Z2s m.+1 z) = z.
Proof.
move=> z m H.
destruct m as [|m] => /=.
- by rewrite H.
- rewrite /bits.adjust_s H bitZ.Z2s_weird /= size_nseq 2!ltnS ltnNge leqnSn /=.
  rewrite !subSS subSnn bitZ.s2Z_true [size _]/= size_nseq.
  by rewrite [bitZ.u2Z _]/= bitZ.u2Z_zeros addZ0.
Qed.

Lemma Z2sK : forall z m, - 2 ^^ m <= z < 2 ^^ m -> s2Z (Z2s m.+1 z) = z.
Proof.
move=> z m [].
case/leZ_eqVlt => H1 H2; by [apply Z2sK_weird | apply Z2sK_not_weird].
Qed.

Lemma Z2s_dis n a b : - 2 ^^ n <= a < 2 ^^ n -> - 2 ^^ n <= b < 2 ^^ n ->
  a <> b -> Z2s n.+1 a <> Z2s n.+1 b.
Proof.
move=> Ha Hb a_b; contradict a_b.
by rewrite -(Z2sK Ha) // -(Z2sK Hb) // a_b.
Qed.

Lemma int_even_and_1_converse : forall n (a : int n), a `& Z2u n 1 = Z2u n 0 -> Zeven (s2Z a).
Proof.
move=> n [] a Ha /= [].
rewrite bits.adjust_u_nil.
rewrite /bits.adjust_u /=.
case: ifP; last first.
  destruct n as [|n].
    by case: a Ha.
  destruct a as [|hd tl] => //.
  destruct n as [|n] => // _.
  rewrite subnn /=.
  destruct tl => //=.
  by destruct hd.
move=> Hn.
destruct n as [|n] => //.
rewrite subSS subn0.
case/lastP : a => // hd tl in Ha *.
rewrite size_rcons in Ha; case: Ha => Ha.
rewrite -cats1 /bits.zext (bits.and_app n) //; last by rewrite size_nseq.
rewrite bits.andl0 //.
destruct tl => [| _].
  rewrite (_ : succn n = n + 1)%nat; last by rewrite addnC.
  rewrite -bits.zeros_app.
  move/eqP.
  by rewrite eqseq_cat // eqxx.
by apply bitZ.Zeven_slstZ_false.
Qed.

Lemma sext_Z2s m z n : - 2 ^^ m <= z < 2 ^^ m -> sext n (Z2s m.+1 z) = Z2s (m.+1 + n) z.
Proof.
move=> [H1 H2].
apply s2Z_inj.
rewrite sext_s2Z // Z2sK // addSn Z2sK // ZpowerD; split.
- apply (@leZ_trans (- 2 ^^ m)) => //.
  rewrite -ZpowerD.
  have ? : 2 ^^ m  <= 2 ^^ (m + n) by apply/leZP; rewrite Zpower_2_le leq_addr.
  omega.
- apply (@ltZ_leZ_trans (2 ^^ m)) => //.
  apply/leZP; by rewrite -ZpowerD Zpower_2_le leq_addr.
Qed.

Lemma s2Z_u2Z_pos : forall l (a : int l), 0 <= s2Z a -> s2Z a = u2Z a.
Proof. move=> l [a Ha] /= H. by eapply bitZ.s2Z_u2Z_pos; eauto. Qed.

Lemma s2Z_u2Z_pos' : forall n (a : int n), 0 <= u2Z a < 2 ^^ n.-1 -> s2Z a = u2Z a.
Proof.
move=> n [a Ha] /= [H1 H2].
eapply bitZ.s2Z_u2Z_pos; eauto.
by rewrite (bitZ.s2Z_u2Z_pos_equiv n a Ha).
Qed.

Lemma s2Z_u2Z_neg : forall n (a : int n), s2Z a < 0 -> u2Z a = s2Z a + 2 ^^ n.
Proof.
move=> n [a Ha] /= H.
move: (bitZ.s2Z_u2Z_neg n a Ha H) => ?; omega.
Qed.

Lemma u2Z_Z2s_neg' : forall (p : positive) n, - 2 ^^ n.-1 < Zneg p < 0 -> 
  u2Z (Z2s n (Zneg p)) = 2 ^^ n - Zpos p.
Proof.
move=> p n H.
destruct n.
- simpl in H.
  assert (Zneg p = - 1) by omega.
  assert (Zneg p = 0) by omega.
  by rewrite H1 in H0.
- simpl u2Z.
  rewrite bits.cplt2_prop; last 2 first.
    case=> x H1.
    move: (bitZ.pos2lst_O p) => H0.
    have H2 : bitZ.u2Z (rev (bitZ.pos2lst p)) = bitZ.u2Z (bits.zeros x).
      by rewrite bitZ.u2Z_zeros H1 bitZ.u2Z_zeros.
    by rewrite bitZ.u2Z_rev_poslst bitZ.u2Z_zeros in H2.
    by case.
  simpl bits.cplt.
  rewrite /bits.adjust_s.
  simpl bitZ.u2Z.
  rewrite bits.size_cplt2.
  have H0 : (0 < Zpos p < 2 ^^ n)%Z.
    rewrite /= in H.
    assert ( Zneg p = - Zpos p) by auto.
    omega.
  have H1 : (Zpos p < 2 ^^ n) by omega.
  destruct n.
  + simpl in H1.
    assert (Zpos p =0) by omega.
    done.
  + move: (bitZ.Z2u_size (Zpos p) n.+1 H1) => H2.
    simpl in H2.
    move: H2; rewrite leq_eqVlt; case/orP => H2; last first.
    * rewrite ltnS H2.
      rewrite bitZ.sext_true bits.size_cplt2 (bitZ.u2Z_cplt2 (size (rev (bitZ.pos2lst p)))) //.
        move: (bitZ.max_u2Z (size (rev (bitZ.pos2lst p))) (rev (bitZ.pos2lst p)) (leqnn _)) => H5.
        rewrite bitZ.u2Z_rev_poslst mulZBr -ZpowerD.
        cutrewrite (size (rev (bitZ.pos2lst p)) + (n.+2 - (size (rev (bitZ.pos2lst p))).+1).+1 = n.+2)%nat.
          ring.
        rewrite size_rev subSS -subSn.
          by rewrite subnKC // ltnW // ltnW // ltnS -size_rev.
        by rewrite ltnW // -size_rev.
      move/(congr1 rev).
      rewrite revK => H3.
      rewrite -bits.rev_zeros revK size_rev in H3.
      by move: (bitZ.pos2lst_O p).
    * rewrite (eqP H2) ltnn subnn [ bitZ.u2Z _]/= bits.size_cplt2 (bitZ.u2Z_cplt2 (size (rev (bitZ.pos2lst p)))) //.
        rewrite (eqP H2) bitZ.u2Z_rev_poslst (ZpowerS 2 n.+1); ring.
      move/(congr1 rev).
      rewrite revK -bits.rev_zeros revK size_rev => H3.
      by move: (bitZ.pos2lst_O p).
Qed.

Lemma Z2s_weird n : u2Z (Z2s n.+1 (- 2 ^^ n)) = 2 ^^ n.
Proof.
by rewrite /= /bits.adjust_s bitZ.size_Z2s_weird /= ltnS ltnNge leqnSn /=
  bitZ.Z2s_weird subSn // subnn /= bitZ.u2Z_zeros size_nseq addZ0.
Qed.

Lemma u2Z_Z2s_neg : forall z n, - 2 ^^ n.-1 <= z < 0 -> u2Z (Z2s n z)  = 2 ^^ n + z.
Proof.
move=> z n [H1 H2].
destruct z => //.
case/leZ_eqVlt : H1 => H1.
- rewrite -H1.
  destruct n => //.
  rewrite Z2s_weird ZpowerS (_ : Peano.pred n.+1 = n) //; ring.
- rewrite (u2Z_Z2s_neg' (conj H1 H2)) -(Zopp_neg p); ring.
Qed.

Lemma u2Z_Z2s_zero : forall n, u2Z (Z2s n Z0) = Z0.
Proof.
move=> n /= .
rewrite /bits.adjust_s /=.
destruct n => //.
destruct n => //.
destruct n => //.
rewrite (_ : (2 < n.+3)%nat = true); last by apply/ltP; omega.
by rewrite /= bitZ.sext_false.
Qed.

Lemma u2Z_Z2s_pos_old : forall z n, 0 < z < 2 ^^ n.-1 -> u2Z (Z2s n z)  = z.
Proof.
destruct z => //; [by move=>n; omega
  | idtac
  | move=> n [H1 H2]; by inversion H1].
move=> n [H1 H2] /=.
rewrite /bits.adjust_s /=.
have X : (size (bitZ.pos2lst p) <= Peano.pred n)%nat.
  by apply bitZ.pos2lst_len.
move: X.
rewrite leq_eqVlt; case/orP => X; last first.
  have Y : ((size (bitZ.pos2lst p)).+1 < n)%nat.
    move/ltP in X.
    apply/ltP; omega.
  rewrite size_rev Y bitZ.sext_false.
  by apply bitZ.u2Z_rev_poslst.
rewrite size_rev (eqP X).
destruct n => //.
  rewrite /= in H2; omega.
rewrite ltnn /= subnn /=.
by apply bitZ.u2Z_rev_poslst.
Qed.

Lemma u2Z_Z2s_pos z n : 0 <= z < 2 ^^ n.-1 -> u2Z (Z2s n z) = z.
Proof.
move=> [H1 H2].
case/leZ_eqVlt : H1 => H1.
  subst z; by rewrite u2Z_Z2s_zero.
by apply u2Z_Z2s_pos_old.
Qed.

(*
Lemma lt_n2Zlt_s2Z : forall n (a b : int n), a `< b -> s2Z a < s2Z b.
Proof.
move=> n [a_lst Ha] [b_lst Hb] /= H.

Lemma listbit_lt_correct_slst2Z : forall n a b, length a = n -> length b = n ->
  listbit_lt a b = true -> [[ a ]]s < [[ b ]]s.
Proof.
elim=> //.
- case=> //; by case.
- move=> n IH [|ha ta] [|hb tb] //.
  case=> Ha; case=> Hb.
  case: ha; case: hb => //=.
  + move=> H.
    move: (IH _ _ Ha Hb H) => X.
    rewrite Ha Hb.
    by apply Zplus_lt_compat_l.
  + move=> _.
    apply ltZ_leZ_trans with (2 ^^ n).
    apply bitZ.max_u2Z.
    by rewrite Ha.
    rewrite Hb.
    move: (min_u2Z tb) => ?; omega.
  - by apply IH.
Qed.

apply listbit_lt_correct with n.
*)

(** correctness of the addition w.r.t. relative integers *)
Lemma s2Z_add: forall n (a b : int n.+1), - 2 ^^ n <= s2Z a + s2Z b < 2 ^^ n -> s2Z (a `+ b) = s2Z a + s2Z b.
Proof. move=> n [a Ha] [b Hb] /= H; by rewrite (bitZ.add_Z n) ?addZ0 // ?subZ0. Qed.

Lemma s2Z_sub: forall n (a b : int n.+1), (- 2 ^^ n <= s2Z a - s2Z b < 2 ^^ n)%Z ->
  s2Z (a `- b) = (s2Z a - s2Z b)%Z.
Proof. move=> n [a Ha] [b Hb] /= H. by rewrite (bitZ.sub_Z n) ?addZ0 // ?subZ0. Qed.

Lemma Z2s_Z2u_0 n : Z2s n 0 = Z2u n 0.
Proof.
destruct n.
  rewrite /Z2s /Z2u.
  apply mk_int_pi => /=; by rewrite bits.adjust_u_nil.
apply s2Z_inj; rewrite Z2sK.
  rewrite s2Z_u2Z_pos' // Z2uK //.
  split => //; exact: expZ_gt0.
  split => //; exact: expZ_gt0.
  split => //; exact: expZ_gt0.
split; last exact: expZ_gt0.
rewrite leZ_oppl oppZ0; exact: expZ_ge0.
Qed.

Lemma Z2s_Z2u_k : forall n k, 0 <= k < 2 ^^ n -> Z2s n k = Z2u n k.
Proof.
elim=> [k /= Hk | n IH k []].
  have {Hk}-> : k = 0 by omega.
  by apply mk_int_pi.
case/leZ_eqVlt => [<- _ | k_lb k_ub].
  by rewrite Z2s_Z2u_0.
rewrite /Z2s /Z2u /=.
rewrite (bitZ.Z2s_Z2u_eq _ _ (conj k_lb k_ub)).
apply mk_int_pi => /=.
rewrite /bits.adjust_s /=.
case: ifP.
  move/ltP/lt_S_n/ltP => size_k.
  rewrite bits.sext_0 /bits.adjust_u.
  move/ltP/lt_S/ltP : (size_k) => ->.
  by rewrite /bits.zext subSS subSn // ltnW.
move/negbT.
rewrite -leqNgt ltnS.
move=> Hcase.
rewrite /bits.adjust_u ltnS.
case: ifP.
  move/leP in Hcase.
  move/leP/(le_antisym _ _ Hcase) => ->.
  by rewrite subnn /= subSn // subnn.
move/negbT.
rewrite -ltnNge => ?.
by rewrite subSn.
Qed.

(** correctness of the signed multiplication w.r.t. relative integers *)
Lemma s2Z_smul : forall n (a b : int n), s2Z (smul a b) = s2Z a * s2Z b.
Proof. move=> n [a Ha] [b Hb] /=; by rewrite (bitZ.smul_Z n). Qed.

Lemma s2Z_shl m n l (x : int l) : (n + S m <= l)%nat ->
  - 2 ^^ m <= s2Z x < 2 ^^ m ->
  s2Z (shl n x) = s2Z x * 2 ^^ n.
Proof.
destruct x as [lst e].
rewrite /shl /s2Z => H H0 /=.
have [H2 | H2] : (- 2 ^^ m <= bitZ.s2Z lst < 0 \/ 0 <= bitZ.s2Z lst < 2 ^^ m) by omega.
- have H1 : (m < l)%nat by ssromega.
  case: (bitZ.s2Z_neg_ones _ _ e _ H1 H2) => x H3.
  have H4 : (l - m > n)%nat by ssromega.
  apply (bitZ.s2Z_shl _ _ e _ _ H4 x) => //; by left.
- have H1 : (m < l)%nat by ssromega.
  case (bitZ.s2Z_u2Z_pos_zeros _ _ e _ H1 H2) => x H4.
  have H3 :(l - m > n)%nat by ssromega.
  apply (bitZ.s2Z_shl _ _ e _ _ H3 x) => //; by right.
Qed.

Lemma bits_shra_neg n : forall (a : int n.+1) m, s2Z a < 0 -> (n <= m)%nat ->
  bits (shra m a) = bits.ones n.+1.
Proof.
case=> a Ha /= m a_neg n_m.
rewrite /shra /bits /= (bitZ.shra_ones _ _ _ Ha a_neg) //.
by rewrite -(cats0 (_ (succn n))) rev_cat bits.rev_ones.
Qed.

Lemma bits_shra_nonneg n : forall (a : int n.+1) m, 0 <= s2Z a -> (n <= m)%nat ->
  bits (shra m a) = bits.zeros n.+1.
Proof.
case=> a Ha /= m a_neg n_m.
rewrite /shra /bits /= (bitZ.shra_zeros _ _ _ Ha a_neg) //.
by rewrite -(cats0 (_ (succn n))) rev_cat bits.rev_zeros.
Qed.

Lemma s2Z_shra_neg n : forall (a : int n.+1) m, s2Z a < 0 -> (n <= m)%nat ->
  shra m a = int_not (Z2u n.+1 0).
Proof.
case=> [a Ha] m a_neg n_m.
apply mk_int_pi => /=.
rewrite cats0 bits.cplt1_zeros (bitZ.shra_ones n) //; by apply/ltP.
Qed.

Lemma s2Z_shra_pos n : forall (a : int n.+1) m, 0 <= s2Z a -> (n <= m)%nat ->
  shra m a = Z2u n.+1 0.
Proof.
case=> [a Ha] m a_neg n_m.
apply mk_int_pi => /=.
rewrite bits.adjust_u_nil (bitZ.shra_zeros n) //; by apply/ltP.
Qed.

Lemma le0concat : forall m n (a : int n), (0 <= s2Z ( `( 0 )_m.+1 `|| a))%Z.
Proof.
move=> m n [a Ha].
rewrite concatE /=.
apply bitZ.min_u2Z.
Qed.

Lemma shrl_sign_bit : forall (n : nat) (a : int (2 ^ n)),
 a `>> (2 ^ n - 1) = Z2u (2 ^ n) 0 \/ a `>> (2 ^ n - 1) = Z2u (2 ^ n) 1.
Proof.
move=> n [a Ha] /=.
have H : bits.shrl (2 ^ n - 1) a = bits.zeros (2 ^ n - 1) ++ head true a :: nil.
  rewrite (bits.shrl_tail (2 ^ n)) //.
  f_equal.
  rewrite subnBA; last by rewrite expn_gt0.
  rewrite addnC addnK.
  destruct a.
    move/esym/eqP : Ha => /=; by rewrite expn_eq0.
  by rewrite /= take0.
  apply/leP; by rewrite subn1 leq_pred.
destruct a.
  suff : False by done.
  move/esym/eqP : Ha => /=; by rewrite expn_eq0.
destruct b; [right | left]; apply mk_int_pi; rewrite H /bits.adjust_u.
- case: ifP => // Hcond.
  destruct n => //.
  by rewrite /= {1}(_ : 1 = 2 ^ 0)%nat // ltn_exp2l in Hcond.
- case: ifP => [ _ | ].
  + rewrite /= /bits.zext subn0 -/bits.zeros -nseqS -subSn; last by rewrite expn_gt0.
    by rewrite subSS subn0 cats0.
  + by rewrite /= expn_gt0.
Qed.

Lemma bZsgn_Zsgn_s2Z : forall (n : nat) (a : int (2 ^ n)), u2Z a <> 0 ->
  bZsgn (u2Z (a `>> (2 ^ n - 1))) = sgZ (s2Z a).
Proof.
move=> n [a Ha] /= a_neq_0.
have -> : bits.shrl (2 ^ n - 1) a = bits.zeros (2 ^ n - 1) ++ head true a :: nil.
  rewrite (bits.shrl_tail (2 ^ n)) //.
    f_equal.
    rewrite subnBA; last by rewrite expn_gt0.
    rewrite addnC addnK.
    destruct a.
      by move/esym : Ha => /eqP /=; rewrite expn_eq0.
    by rewrite /= take0.
  by apply/leP; rewrite subn1 leq_pred.
rewrite bitZ.u2Z_app bits.zeros_app bitZ.u2Z_zeros add0Z.
apply (bitZ.bZsgn_Zsgn_s2Z _ (2 ^ n) _ Ha).
contradict a_neq_0.
by rewrite a_neq_0 bitZ.u2Z_zeros.
Qed.

Lemma le0_or : forall n (a b : int n.+1),
  0 <=? s2Z a -> 0 <=? s2Z b -> 0 <=? s2Z (a `|` b).
Proof.
move=> n [a Ha] [b Hb] //= a_pos b_pos.
case: (bitZ.s2Z_leading_bit_0 _ _ Ha a_pos) => ta [Hta a_ta].
case: (bitZ.s2Z_leading_bit_0 _ _ Hb b_pos) => tb [Htb b_tb].
subst b a => /=.
by apply/leZP/bitZ.min_u2Z.
Qed.

Definition int_break : forall n k q, n = (q * k)%nat ->
  forall (a : int n), list (int k).
Proof.
move=> n k q n_k [a Ha].
apply (fun f => map f (takes k a)) => x.
apply mk_int with (bits.adjust_u x k).
by rewrite bits.size_adjust_u.
Defined.

Lemma size_int_break : forall (n k q : nat) (Hn : n = (q * S k)%nat) (a : int n),
  size (int_break Hn a) = q.
Proof.
move=> n k q Hn [a Ha].
rewrite size_map. by apply len_takes with n.
Qed.

(* TODO: dans l'interface? *)
Lemma int_break_0' n k H a : @int_break n k.+1 0 H a = nil.
Proof.
case: a => a Ha.
subst n.
by rewrite /int_break /= Ha.
Qed.

Lemma int_break_cons :
  forall n k q (v : int n) (H : n = (q.+1 * k)%nat) (H' : (n - k)%nat = (q * k)%nat),
  k <> O ->
  int_break H v =
  Z2u k (u2Z v / 2 ^^ (n - k)) :: int_break H' (Z2u (n - k) (u2Z v)).
Proof.
move => n k q [v H] H0 H1 H2 => /=.
rewrite (bitZ.u2ZK n _ H).
rewrite bits.adjust_u_erase_leading_zeros.
rewrite -{1 2}(cat_take_drop k v) takes_app //=.
- f_equal.
  - apply mk_int_pi.
    rewrite bitZ.u2Z_app.
    rewrite bitZ.u2Z_app_zeros.
    rewrite size_drop H.
    rewrite Z_div_plus_full_l.
    - rewrite Zdiv_small.
      - rewrite Z.add_0_r (bitZ.u2ZK k).
        - by rewrite bits.adjust_u_erase_leading_zeros.
        - rewrite size_take H.
          case: ifP => // /negbT.
          rewrite -leqNgt -subn_eq0 H1 muln_eq0.
          move/eqP : H2 => /negbTE ->; rewrite orbF => /eqP ?; subst q.
          by rewrite H0 mul1n.
      - split.
        - apply bitZ.min_u2Z.
        - apply bitZ.max_u2Z.
          by rewrite size_drop H.
    - move: (expZ_ge1 (n - k)) => ?; omega.
  - do 2 f_equal.
    by rewrite /bits.adjust_u H ltnNge leq_subr /= H0 /= addKn addnK.
        - rewrite size_take H.
          case: ifP => // /negbT.
          rewrite -leqNgt -subn_eq0 H1 muln_eq0.
          move/eqP : H2 => /negbTE ->; rewrite orbF => /eqP ?; subst q.
          by rewrite H0 mul1n.
Qed.

Definition int_flat : forall n k q, n = (q * k)%nat -> list (int k) -> option (int n).
Proof.
move=> n k q n_k lst.
case : (eq_nat_dec (size (flat_map (fun x => int_lst x) lst)) n) => H.
exact (Some (mk_int H)).
exact None.
Defined.

Lemma int_flat_Some : forall n k q (H : n = (q * k)%nat) (l : list (int k)),
  size l = q -> { x | int_flat H l = Some x }.
Proof.
move=> n k q n_q_k l size_l.
rewrite /int_flat.
have H : size (flat_map (fun x0 : int k => int_lst x0) l) = n.
  rewrite (@len_flat_map _ _ q _ k) //; by case.
destruct eq_nat_dec; last by contradiction.
eexists; reflexivity.
Qed.

Lemma int_flat_None : forall n k q (H : n = (q * k)%nat) (l : list (int k)),
  k <> O -> size l <> q -> int_flat H l = None.
Proof.
move=> n k q n_q_k l k_neq0 size_l.
rewrite /int_flat.
have ? : size (flat_map (fun x0 : int k => int_lst x0) l) <> n.
  rewrite (@len_flat_map _ _ (size l) _ k) //.
  - contradict size_l.
    apply/eqP.
    rewrite -(@eqn_pmul2r k); last by rewrite lt0n; apply/eqP.
    by rewrite size_l n_q_k.
  - by case.
by destruct eq_nat_dec.
Qed.

Definition int_flat_ok :
  forall n k q (H: n = (q * k)%nat) (l: list (int k)) (Hl: size l = q), int n.
move => n k q H l Hl.
case: (optionT_dec (@int_flat n k q H l)).
  move => H2.
  destruct H2.
  exact x.
move => H2.
move: (@int_flat_Some n k q H l Hl) => H3.
destruct H3.
rewrite e //= in H2.
Defined.

Lemma int_flat_ok_id : forall n (a : int n) H H', @int_flat_ok n n 1 H (a :: nil) H' = a.
Proof.
move=> n [a Ha] H H'.
rewrite /int_flat_ok /=.
destruct (@optionT_dec (int n)).
  move: s.
  case.
  move=> a'.
  rewrite /int_flat /=.
  destruct eq_nat_dec => //.
  case.
  destruct a' as [a' Ha'].
  case.
  rewrite cats0.
  move=> ?; subst a'.
  by apply mk_int_pi.
suff : False by done.
rewrite /int_flat /= in e.
destruct eq_nat_dec => //.
by rewrite cats0 in n0.
Qed.
    
Lemma int_flat_take : forall n k q (H : n = (q * k)%nat) (l : list (int k)) x x',
  k <> O -> int_flat H l = Some x ->
  int_flat H (take n l) = Some x' -> x = x'.
Proof.
move=> n k q H l x x' Hk.
rewrite /int_flat.
destruct eq_nat_dec; last by done.
destruct eq_nat_dec; last by done.
case => H1 [] H2; subst x x'.
apply mk_int_pi.
rewrite H in e; apply len_flat_map_inv in e => //; last by case.
rewrite H in e0; apply len_flat_map_inv in e0 => //; last by case.
rewrite take_oversize // e H mulnC leq_pmull // lt0n; by apply/eqP.
Qed.

Lemma int_lst_injection : forall n, injection (fun x : int n => int_lst x).
Proof. move=> n [x Hx] [y Hy] /= x_y. by apply mk_int_pi. Qed.

Lemma int_flat_inj n k l1 l2 nk x : n != O -> 
  forall (H : nk = (k * n)%nat),
    int_flat H l1 = Some x -> int_flat H l2 = Some x ->
    l1 = l2.
Proof.
move=> Hk H.
rewrite /int_flat.
destruct eq_nat_dec; last by done.
destruct eq_nat_dec; last by done.
destruct x.
case=> l1_x [] l2_x.
subst lst.
apply flat_map_inj in l2_x => //.
  by apply int_lst_injection.
exists n; split; first by apply/eqP.
by case.
Qed.

Lemma int_flat_ok_inj n k q H l1 Hl1 l2 Hl2 : (k != 0)%nat ->
  @int_flat_ok n k q H l1 Hl1 = @int_flat_ok n k q H l2 Hl2 ->
  l1 = l2.
Proof.
move=> Hk.
rewrite /int_flat_ok.
move: (@int_flat_Some n k q H l1 Hl1) => H1.
move: (@int_flat_Some n k q H l2 Hl2) => H2.
destruct H1; destruct H2.
destruct (optionT_dec (int_flat (k:=k) (q:=q) H l1)); last first.
  by have: False by rewrite e in e1.
destruct (optionT_dec (int_flat (k:=k) (q:=q) H l2)); last first.
  by have: False by rewrite e0 in e1.
destruct s; destruct s0 => Heq; subst x2.
by apply (@int_flat_inj _ _ _ _ _ x1 Hk H).
Qed.

Lemma int_flat_int_flat_ok : forall n k q (Hn : (n = q * k)%nat) a a' H,
  @int_flat n k q Hn a = Some a' -> @int_flat_ok n k q Hn a H = a'.
Proof.
move=> n0 k q Hn a a' H H1.
rewrite /int_flat_ok.
destruct (optionT_dec (int_flat (k:=k) (q:=q) Hn a)); last first.
  by have : False by rewrite H1 in e.
case: s => s Hs.
rewrite H1 in Hs.
by case: Hs.
Qed.

Lemma int_flat_ok_int_flat : forall (n k q : nat) (Hn : (n = q * k)%nat)
  (a : list (int k)) (a' : int n) (H : size a = q),
  int_flat_ok Hn H = a' -> int_flat Hn a = Some a'.
Proof.
move=> n k q Hn a a' H.
rewrite /int_flat_ok.
case: optionT_dec.
  by case=> l Hl ?; subst l.
move=> H'.
move H3 : (int_flat_Some (k:=k) Hn (l:=a) H) => h3.
destruct h3 => {H3}.
suff : False by done.
by rewrite H' in e.
Qed.

(* TODO: move outside *)
Lemma flat_map_id' : forall (q n k : nat) (a : list bool),
  size a = n -> n = (q * S k)%nat ->
  flat_map (fun x0 : int k.+1 => int_lst x0)
  (map
    (fun x0 => mk_int
      (eq_ind_r (fun x => x = k.+1) (refl_equal k.+1)
        (bits.size_adjust_u k.+1 x0))) (takes' k.+1 (size a) a)) = a.
Proof.
elim => [ [] // k [] // | q IHq n k a Ha Hn].
have [ha [ta [ha_ta [Hha Hta]]]] : exists ha ta, a = ha ++ ta /\
  size ha = k.+1 /\ size ta = (q * k.+1)%coq_nat.
  lapply (@app_split _ a k.+1); last first.
    by rewrite Ha Hn mulSn addSn ltnS leq_addr.
  case=> l1 [l2 [Hl1 Hl2]]; exists l1, l2.
  split; first exact Hl2.
  split; first exact Hl1.
  rewrite Hl2 size_cat Hn Hl1 in Ha.
  symmetry in Ha.
  move/plus_minus : Ha => ->.
  by rewrite -{2}(mult_1_l k.+1) -mult_minus_distr_r /= -minus_n_O.
move: {IHq}(IHq _ _ _ Hta (refl_equal _)) => IHq.
move: Ha Hha Hta IHq.
rewrite ha_ta => Ha Hha Hta IHq.
have Sk_neq0 : k.+1 <> O by [].
move: (@takes_app _ _ Sk_neq0 _ ta Hha) => X.
by rewrite -/(takes k.+1 (ha ++ ta)) X /= IHq /bits.adjust_u Hha ltnn subnn drop0.
Qed.

Lemma int_flat_int_break' : forall n k q (a : int n) (Hn : (n = q * S k)%nat),
  int_flat Hn (int_break Hn a) = Some a.
Proof.
move=> n k q [a Ha] /= Hn.
rewrite /int_flat.
set x := flat_map _ _.
destruct eq_nat_dec.
- congr Some.
  apply mk_int_pi.
  by apply flat_map_id' with q n.
- rewrite {}/x in n0.
  rewrite (@len_flat_map _ _ q _ (S k)) in n0.
  rewrite Hn in n0.
  exfalso;  by apply n0.
  by case.
  by rewrite size_map (@len_takes _ _ _ Ha _ _ Hn).
Qed.

Lemma int_flat_int_break : forall n k q (a : int n) (Hn : (n = q * k)%nat),
  int_flat Hn (int_break Hn a) = Some a.
Proof.
move=> n [|k]; last by apply int_flat_int_break'.
move=> q a Hn.
have Hn' : n = O by rewrite Hn muln0; subst n.
subst n.
destruct a as [ [|ha ta] Ha]; last first.
  suff : False by done.
  by rewrite muln0 in Ha.
rewrite /= /int_flat [size _]/=.
destruct eq_nat_dec; last by rewrite muln0 in n.
congr Some; by apply mk_int_pi.
Qed.

(* TODO: move outside *)
Lemma flat_map_nil_inv : forall {A B : Type} (a : list A) (f : A -> list B)
  (Hf : forall a, f a <> nil),
  flat_map f a = nil ->
  a = nil.
Proof.
move=> A B.
elim=> // h t IH f Hf /=.
case/List.app_eq_nil => H.
by move: (Hf h).
Qed.

Lemma int_flat_break : forall q n k (a : list (int k.+1)) (b : int n) (Hn : (n = q * S k)%nat),
  int_flat Hn a = Some b -> int_break Hn b = a.
Proof.
elim.
  move=> n k a [b Hb] Hn.
  rewrite /int_flat.
  destruct eq_nat_dec => //.
  case => a_b.
  subst n.
  destruct b => //=.
  move/size0nil in e.
  apply flat_map_nil_inv in e => //.
  case => /=.
  by case.
move=> q IH n k a b Hn.
rewrite /int_flat.
destruct eq_nat_dec => //.
case.
destruct b as [b Hb].
case => a_b.
rewrite /int_break.
rewrite -(cat_take_drop k.+1 b).
rewrite takes_app //; last by rewrite size_takel // Hb Hn mulSn addSn ltnS leq_addr.
rewrite /=.
destruct a as [|ha ta] => //=.
simpl in e.
subst n.
by destruct b as [|hb tb].
f_equal.
  destruct ha as [ha Hha].
  apply mk_int_pi.
  destruct b as [|hb tb].
    by subst n.
  rewrite /= in a_b.
  rewrite -(cat_take_drop k.+1 (hb :: tb)) in a_b.
  apply cat_inv in a_b; last first.
    by rewrite size_takel // Hb Hn mulSn addSn ltnS leq_addr.
  case: a_b => -> H /=.
  rewrite /= Hn mulSn addSn in Hb.
  rewrite bits.adjust_u_id //= size_takel //.
  case: Hb => ->.
  by rewrite leq_addr.
have Hn0 : (n - k.+1 = q * k.+1)%nat by rewrite Hn -{1}(addn1 q) mulnDl mul1n -addnBA // subnn.
set lst := drop k.+1 b.
have Hlst : size lst = (n - k.+1)%nat by rewrite /lst size_drop Hb.
have [a Ha] : exists a : int (n - k.+1), int_lst a = lst by exists (mk_int Hlst).
move: {IH}(IH (n-k.+1)%nat k ta a Hn0) => IH.
rewrite -{}IH.
  rewrite /int_break /takes -/(drop k.+1 b).
  destruct a.
  simpl in Ha.
  by subst lst0.
rewrite /int_flat.
destruct eq_nat_dec => //.
  f_equal.
  destruct a.
  apply mk_int_pi.
  simpl in a_b.
  simpl in Ha; subst lst0.
  rewrite -(cat_take_drop k.+1 b) in a_b.
  apply cat_inv in a_b; first tauto.
  rewrite size_takel //=.
    by destruct ha.
  by rewrite Hb Hn mulSn addSn ltnS leq_addr.
suff : False by done.
rewrite /= -(cat_take_drop k.+1 b) in a_b.
apply cat_inv in a_b.
case: a_b => a_b a_b'.
rewrite a_b' size_drop Hb Hn in n0.
tauto.
rewrite (size_takel) //.
  by destruct ha.
by rewrite Hb Hn mulSn addSn ltnS leq_addr.
Qed.

Lemma int_break_flat : forall (n k q : nat) (Hn : (n = q * k)%nat)
  (a : list (int k)) (a' : int n) (H : size a = q),
  int_break Hn a' = a -> int_flat Hn a = Some a'.
Proof. move=> q n Hn a a' a_q Ha <-; by apply int_flat_int_break. Qed.

Lemma int_break_0 : forall q n k (H : n = (q * k.+1)%nat),
  int_break H (Z2u n 0) = nseq q (Z2u k.+1 0).
Proof.
elim => [n k H /= | q IH n k H].
  by rewrite mul0n in H; subst n.
rewrite /int_break /= -/(takes k.+1 (bits.adjust_u nil n)) bits.adjust_u_nil.
have H' : (n - k.+1 = q * k.+1)%nat.
  by rewrite H -(addn1 q) mulnDl mul1n -addnBA // subnn addn0.
move: {IH}(IH _ _ H') => <-.
rewrite {1}(_ : n = k.+1 + (n - k.+1))%nat //; last first.
  rewrite subnKC // H -{2}(addn1 k) mulnDr muln1.
  destruct k.
  by rewrite muln0 add0n.
  apply leq_ltn_trans with (q.+1 * k.+1)%nat.
  apply ltn_addr => //.
  by rewrite -{1}(addn0 (q.+1 * _)%nat) ltn_add2l.
rewrite -bits.zeros_app takes_app //=; last by rewrite size_nseq.
f_equal.
+ apply mk_int_pi.
  by rewrite /= bits.adjust_u_nil bits.adjust_u_id //= size_nseq.
+ by rewrite bits.adjust_u_nil.
Qed.

(* TODO: move *)
Definition injection_list n {A B : Type} (f : list A -> B) :=
  forall x y, size x = n -> size y = n -> f x = f y -> x = y.

(* TODO: move *)
Lemma map_inj2 (A B : Type) : forall (f : list A -> B) k, injection_list k f ->
  forall n (a b : list (list A)),
    (forall x, List.In x a -> size x = k) ->
    (forall x, List.In x b -> size x = k) ->
    size a = n -> size b = n ->
  map f a = map f b -> a = b.
Proof.
move=> f k Hf.
elim.
  case=> //; by case.
move=> n IH [|ha ta] // [|hb tb] // x_a x_b [Ha] [Hb] /=.
case.
move=> H.
apply Hf in H; last 2 first.
  apply x_a.
  by simpl; left.
  apply x_b.
  by simpl; left.
subst hb.
move=> H.
apply IH in H => //.
  by rewrite H.
move=> x hx.
apply x_a.
by rewrite /=; right.
move=> x hx.
apply x_b.
by rewrite /=; right.
Qed.

Lemma int_break_inj : forall n k nk (l1 l2 : int nk) ,
  n <> O -> forall (H : nk = (k * n)%nat),
  int_break H l1 = int_break H l2 ->
  l1 = l2.
Proof.
move=> n k nk [l1 H1] [l2 H2] Hn H.
rewrite /int_break.
move=> K.
apply mk_int_pi.
destruct n; first by done.
move: (len_takes H1 H) => K1.
move: (len_takes H2 H) => K2.
apply map_inj2 with (n := k) (k := n.+1) in K => //; last first.
  move=> x0 H'.
  by apply (@In_takes _ nk _ H2 _ k) in H' => //.
  move=> x0 H'.
  by apply (@In_takes _ nk _ H1 _ k) in H' => //.
  rewrite /injection_list => a b Ha Hb.
  case.
  by rewrite /bits.adjust_u Ha Hb ltnn subnn /= !drop0.
apply (@takes_inj _ k n.+1 nk) in K => //.
by rewrite mulnC.
Qed.

Lemma add_Z2s {n} : forall a b, Z2s n.+3 a `+ Z2s n.+3 b = Z2s (n.+3) (a + b).
Proof.
move=> a b.
rewrite /Z2s.
apply mk_int_pi => /=.
case: (Z_zerop a) => a0.
  subst a.
  by rewrite bitZ.adjust_s_Z2s_0 bits.addC bits.addl0 // bits.size_adjust_s.
case: (Z_zerop b) => b0.
  subst b.
  rewrite bitZ.adjust_s_Z2s_0 bits.addl0.
  by rewrite addZ0.
  by rewrite bits.size_adjust_s.
case/not_Zeq_inf : a0 => a0; last first.
Abort.

Lemma add_Z2s {n} : forall a b,
  Z2s n.+1 a `+ Z2s n.+1 b = Z2s n.+1 (a + b).
Proof.
move=> a b.
apply s2Z_inj.
case: (Z_lt_le_dec (a + b) (2 ^^ n)) => ab_top.
  case: (Z_le_gt_dec (-2 ^^ n) (a + b)) => ab_bot.
    rewrite Z2sK //.
    case: (Z_lt_le_dec a (2 ^^ n)) => a_top.
      case: (Z_le_gt_dec (-2 ^^ n) a) => a_bot.
        case: (Z_lt_le_dec b (2 ^^ n)) => b_top.
          case: (Z_le_gt_dec (-2 ^^ n) b) => b_bot.
            rewrite s2Z_add; by rewrite Z2sK // Z2sK.
          clear b_top.

Lemma s2Z_Z2s_underflow : forall n (b : Z),
  - 2 ^^ n.+1 <= b < -2 ^^ n -> s2Z (Z2s n.+1 b) = b + 2 ^^ n.+1.
Proof.
Abort.

Abort.

Local Close Scope machine_int_scope.

End MachineInt.

Import MachineInt.

Local Open Scope machine_int_scope.

Lemma min_u2Zb n (a : int n) : 0 <=? u2Z a.
Proof. apply/leZP. by apply min_u2Z. Qed.

(* TODO: generalize to n = 0? *)
Lemma Z2s_s2Z: forall n x, Z2s n.+1 (s2Z x) = x.
Proof.
move=> n x.
apply s2Z_inj.
rewrite Z2sK //.
split; by [apply min_s2Z | apply max_s2Z].
Qed.

Lemma Z2s_2complement: forall n x, -2 ^^ n.-1 <= x < 2 ^^ n.-1 ->
  Z2s n x = Z2u n (if Z_lt_dec x 0 then 2 ^^ n + x else x).
Proof.
move => n x [H H0].
case: Z_lt_dec => H1 /=.
- by rewrite -u2Z_Z2s_neg // Z2u_u2Z.
- apply Z2s_Z2u_k; split.
  - exact/leZNgt.
  - apply (@ltZ_leZ_trans (2 ^^ n.-1)) => //.
    apply/leZP; by rewrite Zpower_2_le leq_pred.
Qed.

(* TODO: try to use as much as possible *)
Lemma sext_0 n m : sext n (Z2u m 0) = Z2u (m + n) 0.
Proof.
apply u2Z_inj.
rewrite u2Z_sext.
- rewrite Z2uK.
  + rewrite Z2uK //.
    split => //; exact: expZ_gt0.
  + split => //; exact: expZ_gt0.
- split; first exact: min_u2Z.
  rewrite Z2uK.
  + exact: expZ_gt0.
  + split => //; exact: expZ_gt0.
Qed.

Local Open Scope eqmod_scope.

Lemma add0i n x : Z2u n 0 `+ x = x.
Proof.
apply u2Z_inj.
rewrite u2Z_add.
- rewrite Z2uK.
  + exact: add0Z.
  + split => //; exact: expZ_gt0.
- rewrite Z2uK.
  + rewrite add0Z; exact: max_u2Z.
  + split => //; exact: expZ_gt0.
Qed.

Lemma add_reg {n} : forall (a b k : int n), a `+ k = b `+ k -> a = b.
Proof.
move=> a b k H.
have H' : u2Z (a `+ k) = u2Z (b `+ k) by rewrite H.
case: (Z_lt_le_dec (u2Z a + u2Z k) (2 ^^ n)) => ak.
  rewrite u2Z_add // in H'.
  case: (Z_lt_le_dec (u2Z b + u2Z k) (2 ^^ n)) => bk.
    rewrite u2Z_add // in H'.
    apply u2Z_inj; omega.
  move: (@u2Z_add_overflow _ _ _ bk) => H''.
  have H3 : u2Z (b `+ k) = u2Z b + u2Z k - 2 ^^ n by omega.
  rewrite {}H3 in H'.
  apply u2Z_inj.
  have abs : u2Z a = u2Z b - 2 ^^ n by omega.
  move: (min_u2Z a) => ?. move: (min_u2Z b) => ?. move: (max_u2Z a) => ?. move: (max_u2Z b) => ?.
  omega.
move: (@u2Z_add_overflow _ _ _ ak) => H''.
have H3 : u2Z (a `+ k) = u2Z a + u2Z k - 2 ^^ n by omega.
rewrite {}H3 in H'.
case: (Z_lt_le_dec (u2Z b + u2Z k) (2 ^^ n)) => bk.
  rewrite u2Z_add // in H'.
  have abs : u2Z a - 2 ^^ n = u2Z b by omega.
  move: (min_u2Z a) => ?. move: (min_u2Z b) => ?. move: (max_u2Z a) => ?. move: (max_u2Z b) => ?.
  omega.
move: (@u2Z_add_overflow _ _ _ bk) => H'''.
have H4 : u2Z (b `+ k) = u2Z b + u2Z k - 2 ^^ n by omega.
rewrite {}H4 in H'.
apply u2Z_inj; omega.
Qed.

Lemma sub_reg {n} : forall (a b k : int n), a `- k = b `- k -> a = b.
Proof.
move=> a b k H.
have H' : u2Z (a `- k) = u2Z (b `- k) by rewrite H.
case: (Z_lt_le_dec (u2Z a) (u2Z k)) => ak; last first.
  rewrite u2Z_sub in H'; last by apply Zle_ge.
  case: (Z_lt_le_dec (u2Z b) (u2Z k)) => bk; last first.
    rewrite u2Z_sub in H'; last by apply Zle_ge.
    apply u2Z_inj; omega.
  rewrite u2Z_sub_overflow // in H'.
  apply u2Z_inj.
  move: (min_u2Z a) => ?. move: (min_u2Z b) => ?. move: (max_u2Z a) => ?. move: (max_u2Z b) => ?.
  omega.
rewrite u2Z_sub_overflow // in H'.
case: (Z_lt_le_dec (u2Z b) (u2Z k)) => bk; last first.
  rewrite u2Z_sub in H'; last by apply Zle_ge.
  move: (min_u2Z a) => ?. move: (min_u2Z b) => ?. move: (max_u2Z a) => ?. move: (max_u2Z b) => ?.
  omega.
rewrite u2Z_sub_overflow // in H'.
apply u2Z_inj; omega.
Qed.

Lemma u2Z_add_eqmod n (a b : int n) : u2Z (a `+ b) =m u2Z a + u2Z b {{ 2^^n }}.
Proof.
elim (Z_le_gt_dec (2 ^^ n) (u2Z a + u2Z b)) => H.
- exists (-1)%Z.
  rewrite -(u2Z_add_overflow H); ring.
- exists 0.
  rewrite mul0Z addZ0; apply u2Z_add; omega.
Qed.

Lemma add_Z2u l a b : 0 <= a -> 0 <= b -> Z2u l a `+ Z2u l b = Z2u l (a + b).
Proof.
move=> Ha Hb.
apply u2Z_inj.
case: (Z_lt_le_dec (u2Z (Z2u l a) + u2Z (Z2u l b)) (2 ^^ l)) => Hadd.
- rewrite u2Z_add //.
  case: (Z_lt_le_dec (a + b) (2 ^^ l)) => HZ2u.
  + symmetry; rewrite Z2uK; last by omega.
    do 2 (rewrite Z2uK //; last by omega).
  + symmetry; rewrite u2Z_Z2u_Zmod; last by omega.
    case: (Z_lt_le_dec a (2 ^^ l)) => HA.
    rewrite Z2uK // in Hadd *.
    * case: (Z_lt_le_dec b (2 ^^ l)) => HB.
      - rewrite Z2uK // in Hadd; omega.
      - rewrite u2Z_Z2u_Zmod // in Hadd *.
        rewrite -(Zmod_small (a + b mod 2 ^^ l) (2 ^^ l)); last first.
          move: (Z_mod_lt b _ (Zlt_gt _ _ (expZ_gt0 l))) => ?; omega.
        by rewrite Zplus_mod_idemp_r.
    * rewrite u2Z_Z2u_Zmod // in Hadd *.
      case: (Z_lt_le_dec b (2 ^^ l)) => HB.
     - rewrite Z2uK // in Hadd *.
        rewrite -(Zmod_small (a mod 2 ^^ l + b) (2^^l)); last first.
          move: (Z_mod_lt a _ (Zlt_gt _ _ (expZ_gt0 l))) => ?; omega.
        by rewrite Zplus_mod_idemp_l.
      - rewrite u2Z_Z2u_Zmod // in Hadd *.
        rewrite -(Zmod_small (a mod 2 ^^ l + b mod 2 ^^ l) (2 ^^ l)); last first.
          move: (Z_mod_lt a _ (Zlt_gt _ _ (expZ_gt0 l))) => ?;
            move: (Z_mod_lt b _ (Zlt_gt _ _ (expZ_gt0 l))) => ?; omega.
        by rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r.
- move: (u2Z_add_overflow Hadd) => H.
  have {H}-> : u2Z (Z2u l a `+ Z2u l b) = u2Z (Z2u l a) + u2Z (Z2u l b) - 2 ^^ l by omega.
  case: (Z_lt_le_dec (a + b) (2 ^^ l)) => HZ2u.
  + symmetry; rewrite Z2uK; last by omega.
    do 2 (rewrite Z2uK // in Hadd; last by omega).
    omega.
  + symmetry; rewrite u2Z_Z2u_Zmod //; last by omega.
    case: (Z_lt_le_dec a (2 ^^ l)) => HA.
    rewrite Z2uK // in Hadd *.
    * case: (Z_lt_le_dec b (2 ^^ l)) => HB.
      - rewrite {Hadd}Z2uK //.
        have H' : 0 <= a + b - 2 ^^ l < 2 ^^ l by omega.
        rewrite -(Zmod_small (a + b - 2 ^^ l) (2^^l)) //.
        have -> : a + b - 2 ^^ l = (a + b ) + ( -1) * 2 ^^ l by ring.
        by rewrite Z_mod_plus_full.
      - rewrite u2Z_Z2u_Zmod // in Hadd *.
        have H' : 0 <= a + b mod 2 ^^ l - 2 ^^ l < 2 ^^ l.
          move: (Z_mod_lt b _ (Zlt_gt _ _ (expZ_gt0 l))) => X; omega.
        rewrite -(Zmod_small (a + b mod 2 ^^ l - 2 ^^ l) (2^^l)) //.
        have -> : a + b mod 2 ^^ l - 2 ^^ l = (a + b mod 2 ^^ l) + ( -1) * 2 ^^ l by ring.
        by rewrite Z_mod_plus_full Zplus_mod_idemp_r.
    * rewrite u2Z_Z2u_Zmod // in Hadd *.
      case: (Z_lt_le_dec b (2 ^^ l)) => HB.
      - rewrite Z2uK // in Hadd *.
        have H' : 0 <= a mod 2 ^^ l + b - 2 ^^ l < 2 ^^ l.
          move: (Z_mod_lt a _ (Zlt_gt _ _ (expZ_gt0 l))) => X; omega.
        rewrite -(Zmod_small (a mod 2 ^^ l + b - 2 ^^ l) (2^^l)) //.
        have -> : a mod 2 ^^ l + b - 2 ^^ l = (a mod 2 ^^ l + b) + ( -1) * 2 ^^ l by ring.
        by rewrite Z_mod_plus_full Zplus_mod_idemp_l.
      - rewrite u2Z_Z2u_Zmod // in Hadd *.
        have H' : 0 <= a mod 2 ^^ l + b mod 2 ^^ l - 2 ^^ l < 2^^l.
          move: (Z_mod_lt a _ (Zlt_gt _ _ (expZ_gt0 l))) => X;
            move: (Z_mod_lt b _ (Zlt_gt _ _ (expZ_gt0 l))) => Y; omega.
        rewrite -(Zmod_small (a mod 2 ^^ l + b mod 2 ^^ l - 2 ^^ l) (2^^l)) //.
        have -> : a mod 2 ^^ l + b mod 2 ^^ l - 2 ^^ l = (a mod 2 ^^ l + b mod 2 ^^ l) + ( -1) * 2 ^^ l by ring.
        by rewrite Z_mod_plus_full Zplus_mod_idemp_l Zplus_mod_idemp_r.
Qed.

Lemma u2Z_add_Z2u : forall n (a : int n) b, 0 <= b -> u2Z a + b < 2 ^^ n ->
  u2Z (a `+ Z2u n b) = u2Z a + b.
Proof.
move=> n a b H H'.
have H'' : 0 <= b < 2 ^^ n.
  split => //; move: (min_u2Z a) => X; omega.
by rewrite u2Z_add Z2uK.
Qed.

Lemma u2Z_add_Z_of_nat : forall n (a : int n) b,
  u2Z a + Z_of_nat b < 2 ^^ n -> u2Z (a `+ Z2u n (Z_of_nat b)) = u2Z a + Z_of_nat b.
Proof. move=> n a b H. apply u2Z_add_Z2u => //. by apply Zle_0_nat. Qed.

Lemma u2Z_add_Z2s : forall n (a : int n.+1) b,
  - 2 ^^ n < b < 0 -> 0 <= u2Z a + b -> u2Z (a `+ Z2s n.+1 b) = u2Z a + b.
Proof.
move=> n a b H H'.
destruct b => //.
- omega.
- case: H => H; by destruct p.
- apply (@eqZ_add2l (2 ^^ n.+1)).
  rewrite addZC u2Z_add_overflow; last first.
    rewrite addZC s2Z_u2Z_neg; last first.
      rewrite Z2sK; omega.
    rewrite Z2sK; omega.
  rewrite u2Z_Z2s_neg //; last by rewrite /=; omega.
  have -> : Zneg p = - Zpos p by rewrite -Zopp_neg oppZK.
  ring.
Qed.

Lemma u2Z_add_Z2u_overflow : forall l (a : int (S l)), u2Z (a `+ Z2u (S l) 1) = 0 ->
  u2Z a = 2 ^^ (S l) - 1.
Proof.
move=> l a H.
have [//|X] : u2Z a = 2 ^^ (S l) - 1 \/ u2Z a < 2 ^^ (S l) - 1.
  move: (max_u2Z a) => X; move: (min_u2Z a) => Y; omega.
rewrite u2Z_add in H; last first.
  rewrite Z2uK; first by omega.
  split => //.
  rewrite (_ : 1 = 2 ^^ 0) //.
  apply expZ_2_lt => //; by apply lt_O_Sn.
rewrite Z2uK in H; last first.
  split => //.
  rewrite (_ : 1 = 2 ^^ 0) //.
  apply expZ_2_lt => //; by apply lt_O_Sn.
move: (min_u2Z a) => ?; omega.
Qed.

Lemma u2Z_add_plus_u2Z_s2Z n (a b : int n) : 0 <= u2Z a + s2Z b < 2 ^^ n ->
  u2Z (a `+ b) = u2Z a + s2Z b.
Proof.
move=> H.
case: (Z_lt_ge_dec (s2Z b) 0) => H0.
- move: (s2Z_u2Z_neg H0) => H1.
  have H2 : u2Z (add a b) + 2 ^^ n = u2Z a + s2Z b + 2 ^^ n.
    rewrite -addZA -H1 u2Z_add_overflow //; omega.
  omega.
- have H1 : s2Z b = u2Z b.
    apply s2Z_u2Z_pos; omega.
  rewrite H1 in H *.
  apply u2Z_add; omega.
Qed.

Lemma lt_n_irrefl n (a : int n) : ~ a `< a.
Proof. move/lt_n2Zlt. by move: (ltZZ (u2Z a)). Qed.

Lemma u2Z_add_no_overflow n (a b : int n) : u2Z a <= u2Z (a `+ b) ->
  u2Z a + u2Z b < 2 ^^ n.
Proof.
intros H.
case: (Z_lt_ge_bool (u2Z a + u2Z b) (2 ^^ n)) => x H0; destruct x => //.
lapply (@u2Z_add_overflow _ a b); last by omega.
intro H1.
assert (u2Z (add a b) = u2Z a + u2Z b - 2 ^^ n) by omega.
rewrite H2 in H.
assert ( 2^^n <= u2Z b ) by omega.
generalize (max_u2Z b); intro; omega.
Qed.

Lemma u2Z_add_overflow' n (a b: int n) : u2Z (a `+ b) < u2Z a ->
  2^^n <= u2Z a + u2Z b.
Proof.
intros H.
case: (Z_lt_ge_bool (u2Z a + u2Z b) (2 ^^ n)) => x H0; destruct x.
- lapply (@u2Z_add _ a b) => //.
  intro.
  rewrite H1 in H.
  generalize (min_u2Z b); intro.
  assert (u2Z b = 0) by omega.
  rewrite H3 in H; omega.
- omega.
Qed.

Lemma u2Z_add_mod' (n : nat) (a : int n) m k :
  0 <= k -> (u2Z a) mod m = 0 ->
  0 <= k * m -> (2 ^^ n) mod m = 0 ->
  u2Z (a `+ Z2u n (k * m)) mod m = 0.
Proof.
move=> k_pos a_m km_pos m_n.
case/leZ_eqVlt : km_pos => km_pos.
  move/esym/eqP : km_pos; rewrite mulZ_eq0 => /orP[|] /eqP ?.
  subst k; by rewrite mul0Z addi0.
  subst m; by rewrite mulZ0 addi0.
rewrite (_ : 0 = 0 mod m) //.
have m_min' : 0 < m.
  destruct m => //.
  by rewrite mulZ0 in km_pos.
  lapply (Zmult_sign k (Zneg p) k_pos) => //.
  omega.
apply (proj1 (eqmod_Zmod _ _ _ m_min')).
eapply eqmod_trans with (u2Z a + u2Z (Z2u n (k * m))).
- apply Zmod_divides in m_n; last by omega.
  case: m_n => c m_n.
  apply eqmod_div with c.
  rewrite (mulZC c m) -m_n.
  by apply u2Z_add_eqmod.
- apply Zmod_divides in a_m; last by omega.
  case: a_m => c Hc.
  rewrite u2Z_Z2u_Zmod; last by omega.
  apply eqmod_trans with (u2Z a); last first.
  exists c; by rewrite mulZC.
  rewrite Hc.
  rewrite addZC.
  rewrite -{2}(add0Z (m * c)).
  apply eqmod_compat_plus_R.
  apply Zmod_divides in m_n; last by omega.
  case: m_n => q m_n.
  apply (proj2 (eqmod_Zmod _ _ _ m_min')).
  by rewrite m_n mulZC Zmult_mod_distr_l mulZC Z_mod_mult Zmod_0_l.
Qed.

Lemma u2Z_add_mod n (a : int n) m : (u2Z a) mod m = 0 -> 0 <= m ->
  (2 ^^ n) mod m = 0 ->
  u2Z (a `+ Z2u n m) mod m = 0.
Proof.
move=> Ha Hm n_m.
rewrite -{1}(mul1Z m).
apply u2Z_add_mod' => //.
by rewrite mul1Z.
Qed.

Definition scale n (a : int n) m (k : nat) : int n :=
  a `+ Z2u n (Z_of_nat (m * k)).

Definition add_prod n (a : int n) m (k : Z) : int n :=
  if 0 <=? k then
    a `+ Z2u n (Z<=nat m * k)
  else
    a `+ cplt2 (Z2u n (Z<=nat m * `|k|)).

Lemma add_prodC n (a : int n) (m : nat) (b : Z) (c : Z) :
  add_prod (add_prod a m b) m c = add_prod (add_prod a m c) m b.
Proof.
rewrite /add_prod.
case: ifP => Hc; case: ifP => Hb; by rewrite (addC a) addA addC.
Qed.

Lemma add_prod_assoc' n (a b c : int n.+1) m :
  0 <= Z<=nat m.+1 * s2Z b < 2 ^^ n ->
  0 <= Z<=nat m.+1 * s2Z c < 2 ^^ n ->
  0 <= Z<=nat m.+1 * s2Z b + Z<=nat m.+1 * s2Z c < 2 ^^ n ->
  add_prod (add_prod a m.+1 (s2Z b)) m.+1 (s2Z c) = add_prod a m.+1 (s2Z (b `+ c)).
Proof.
move=> b_bound c_bound bc_bound.
have b0 : (0 <= s2Z b)%Z.
  move: b_bound.
  rewrite Z_S.
  case => /Zle_0_mult_inv ? _; omega.
have c0 : (0 <= s2Z c)%Z.
  move: c_bound.
  rewrite Z_S.
  case => /Zle_0_mult_inv ? _; omega.
have b_add_c : (0 <= s2Z b + s2Z c < 2 ^^ n)%Z.
  move: bc_bound; clear.
  rewrite -mulZDr.
  case => /Zle_0_mult_inv bc_bound0 bc_bound.
  case: bc_bound0 => bc_bound0; last first.
    rewrite Z_S in bc_bound0.
    omega.
  split; first by tauto.
  rewrite mulZC in bc_bound.
  apply Zlt_Zmult_inv' in bc_bound => //.
  tauto.
  exact: expZ_ge0.
have b_bound_weak : 0 <= Z<=nat m.+1 * s2Z b < 2 ^^ n.+1.
  split; first by omega.
  exact/(ltZ_trans (proj2 b_bound))/expZ_2_lt.
have c_bound_weak : 0 <= Z<=nat m.+1 * s2Z c < 2 ^^ n.+1.
  split; first by omega.
  exact/(ltZ_trans (proj2 c_bound))/expZ_2_lt.
have Hbc_bound_weak : 0 <= Z<=nat m.+1 * (s2Z b + s2Z c) < 2 ^^ n.+1.
  rewrite -mulZDr in bc_bound.
  split; first by case: bc_bound.
  exact/(ltZ_trans (proj2 bc_bound))/expZ_2_lt.
rewrite /add_prod.
move/leZP : (c0) => ->.
move/leZP : (b0) => ->.
have s2Z_b_add_c : (s2Z (b `+ c) = s2Z b + s2Z c)%Z.
    rewrite s2Z_add; last first.
      rewrite Z_S in b_bound.
      rewrite Z_S in c_bound.
      rewrite Z_S in bc_bound.
      suff Hsuff : (0 <= s2Z b + s2Z c < 2 ^^ n)%Z.
        split => //.
        apply: (leZ_trans _ (proj1 Hsuff)).
        omega.
        rewrite -mulZDr in bc_bound.
        tauto.
      exact b_add_c.
    by rewrite -mulZDr in bc_bound.
have -> : 0 <=? s2Z (b `+ c) by apply/leZP; omega.
rewrite addA.
f_equal.
apply u2Z_inj.
rewrite Z2uK; last first.
  rewrite s2Z_b_add_c.
  by rewrite -mulZDr in bc_bound.
rewrite u2Z_add; last first.
  rewrite mulZDr in Hbc_bound_weak.
  rewrite !Z2uK //; tauto.
rewrite !Z2uK // s2Z_add.
- ring.
- split; last by tauto.
  apply: (leZ_trans _ (proj1 b_add_c)).
  omega.
Qed.

Lemma add_prodA : forall n (a b c : int n.+1) m,
  (0 < m)%nat ->
  0 <= Z<=nat m * s2Z b < 2 ^^ n ->
  0 <= Z<=nat m * s2Z c < 2 ^^ n ->
  0 <= Z<=nat m * s2Z b + Z<=nat m * s2Z c < 2 ^^ n ->
  add_prod (add_prod a m (s2Z b)) m (s2Z c) = add_prod a m (s2Z (b `+ c)).
Proof. destruct m => // Hm. by apply add_prod_assoc'. Qed.

Lemma scale_mod n (a : int n) m :
  u2Z a mod (Z<=nat m) = 0 ->
  2 ^^ n mod (Z<=nat m) = 0 ->
  forall k, u2Z (scale a m k) mod (Z<=nat m) = 0.
Proof.
move=> H H1 k.
rewrite /scale.
rewrite inj_mult mulZC.
apply u2Z_add_mod' => //.
by apply Zle_0_nat.
rewrite -inj_mult; by apply Zle_0_nat.
Qed.

Lemma add_prod_inj n (a : int n) m (k l : Z) : (0 < m)%nat ->
  Z<=nat m * `|k| < 2 ^^ n -> Z<=nat m * `|l| < 2 ^^ n ->
  sgZ k = sgZ l ->
  add_prod a m k = add_prod a m l -> k = l.
Proof.
move=> Hm mk ml kl.
rewrite /add_prod.
case: ifP => Hk.
  case: ifP => Hl.
    rewrite 2!(addC a).
    move/add_reg.
    have {mk}mk : (0 <= Z<=nat m * k < 2 ^^ n)%Z.
      rewrite (Z.abs_eq k) in mk; last exact/leZP.
      split => //.
      move/leZP in Hk.
      apply mulZ_ge0 => //; exact: Zle_0_nat.
    have {ml}ml : (0 <= Z<=nat m * l < 2 ^^ n)%Z.
      rewrite (Z.abs_eq l) in ml; last exact/leZP.
      split => //.
      move/leZP in Hl.
      apply mulZ_ge0 => //; exact: Zle_0_nat.
    move/(Z2u_inj mk ml)/Z.mul_reg_l.
    apply.
    move/Z_of_nat_0 => ?; by subst.
  exfalso.
  rewrite (Z.sgn_neg l) in kl; last by move/leZP in Hl; omega.
  rewrite -> Z.sgn_neg_iff in kl.
  move/leZP in Hk; omega.
case: ifP => Hl.
  rewrite (Z.sgn_neg k) in kl; last by move/leZP in Hk; omega.
  symmetry in kl.
  rewrite -> Z.sgn_neg_iff in kl.
  move/leZP in Hl; omega.
rewrite 2!(addC a).
move/add_reg/cplt2_inj.
have {mk}mk : (0 <= Z<=nat m * `|k| < 2 ^^ n)%Z.
  split => //; apply mulZ_ge0; by [apply Zle_0_nat | apply normZ_ge0].
have {ml}ml : (0 <= Z<=nat m * `|l| < 2 ^^ n)%Z.
  split => //; apply mulZ_ge0; by [apply Zle_0_nat | apply normZ_ge0].
move/(Z2u_inj mk ml)/Z.mul_reg_l => H.
have : Z<=nat m <> Z0 by move/Z_of_nat_0 => ?; subst.
case/H/Z.abs_eq_cases => //.
move=> ?; subst k.
exfalso.
move/leZP in Hl; move/leZP in Hk; omega.
Qed.

Lemma add_n_lt_n : forall n (a b : int n.+1), a `< b ->
  a `+ Z2u n.+1 1 `<= b.
Proof.
move=> l a b H.
have [X|Z] : u2Z a + u2Z (Z2u (S l) 1) < 2^^(S l) \/ 2^^(S l) <= u2Z a + u2Z (Z2u (S l) 1) by omega.
- apply lt_n2Zlt in H.
  apply Zle2le_n.
  rewrite u2Z_add // Z2uK; first by omega.
  split => //.
  rewrite (_ : 1 = 2 ^^ 0) //.
  apply expZ_2_lt => //; by apply lt_0_Sn.
- apply lt_n2Zlt in H.
  apply Zle2le_n.
  move: (u2Z_add_overflow Z) => X.
  have Y : u2Z a + u2Z (Z2u (S l) 1) - 2 ^^ (S l) <= u2Z b.
    rewrite Z2uK.
    move: (expZ_gt0 l.+1) => ?; omega.
    split => //.
    rewrite (_ : 1 = 2 ^^ 0) //.
    exact: expZ_2_lt.
  omega.
Qed.

Lemma max_u2Z_umul l (a b : int l) : u2Z (a `* b) <= (2 ^^ l - 1) * (2 ^^ l - 1).
Proof.
rewrite u2Z_umul.
apply leZ_pmul; [exact: min_u2Z | exact: min_u2Z | | ].
move: (max_u2Z a) => ?; omega.
move: (max_u2Z b) => ?; omega.
Qed.

Lemma umulA : forall l (a b c : int l), (a `* b) `* zext l c = zext l a `* (b `* c).
Proof.
move=> *; apply u2Z_inj.
rewrite u2Z_umul u2Z_zext u2Z_umul u2Z_umul u2Z_zext u2Z_umul; ring.
Qed.

Lemma umul_add_distr : forall l (a b c : int l), u2Z b + u2Z c < 2 ^^ l ->
  a `* (b `+ c) = (a `* b) `+ (a `* c).
Proof.
intros.
apply u2Z_inj.
rewrite u2Z_umul u2Z_add // u2Z_add.
rewrite 2!u2Z_umul; ring.
rewrite 2!u2Z_umul ZpowerD -mulZDr.
destruct l.
- rewrite /= in H *.
  have H0 : u2Z b + u2Z c = 0.
    move: (min_u2Z b) => X; move: (min_u2Z c) => Y; omega.
  by rewrite mulZC /= H0.
- case/boolP : (u2Z a == 0) => [/eqP|] H1.
  + rewrite H1 -ZpowerD mul0Z; exact: expZ_gt0.
  + case/boolP : (u2Z b + u2Z c == 0) => /eqP H2.
    * rewrite H2 mulZ0 -ZpowerD; exact: expZ_gt0.
    * apply (@ltZ_trans (2 ^^ (S l) * (u2Z b + u2Z c))).
      - apply ltZ_pmul2r.
        move: (min_u2Z b) (min_u2Z c) => ? ?; omega.
        exact: max_u2Z.
      - rewrite mulZC.
        apply ltZ_pmul2r => //; exact: expZ_gt0.
Qed.

Lemma shl_0 n m : shl n (Z2u m 0) = Z2u m 0.
Proof.
apply u2Z_inj.
case: (le_lt_dec n m) => H.
- rewrite (@u2Z_shl _ _ _ (m - n)).
  + rewrite Z2uK //.
    split => //; exact: expZ_gt0.
  + rewrite subnKC //; by apply/leP.
  + rewrite Z2uK.
    - exact: expZ_gt0.
    - split => //; exact: expZ_gt0.
- rewrite u2Z_shl_overflow; last first.
    apply/ltnW; by apply/ltP.
  rewrite Z2uK //.
  split => //; exact: expZ_gt0.
Qed.

Lemma shl_Z2u : forall l (a : int l) k, shl k a = Z2u l (u2Z a * 2 ^^ k).
Proof.
move=> l a k; apply u2Z_inj.
case: (le_lt_dec l k) => Hlk.
- rewrite u2Z_shl_overflow //; last by apply/leP.
  have [Ha0 | Ha0] : u2Z a = 0 \/ 0 < u2Z a.
  + move: (min_u2Z a) => X; omega.
  + rewrite Ha0 /= Z2uK //.
    split => //; exact: expZ_gt0.
  + rewrite u2Z_Z2u_Zmod; last first.
      apply (@leZ_trans (1 * 2 ^^ k)).
      * rewrite mul1Z; exact: expZ_ge0.
      * apply leZ_wpmul2r; [exact: expZ_ge0 | omega].
    have -> : 2 ^^ k = 2 ^^ (k - l) * 2 ^^ l.
    rewrite -ZpowerD subnK //; exact/leP.
    by rewrite mulZA Z_mod_mult.
- have [Ha|Ha] : (u2Z a < 2 ^^ (l - k)) \/ (2 ^^ (l - k) <= u2Z a) by omega.
  + rewrite (@u2Z_shl _ _ _ (l - k)) //; last first.
      rewrite subnKC //; exact/ltnW/leP.
    rewrite Z2uK //; split.
    * apply mulZ_ge0; by [apply min_u2Z | exact: expZ_ge0].
    * apply (@ltZ_leZ_trans (2 ^^ (l - k) * 2 ^^ k)).
        apply ltZ_pmul2r => //; exact: expZ_gt0.
      rewrite -ZpowerD subnK //; [exact: leZZ | exact/ltnW/ltP].
  + rewrite u2Z_Z2u_Zmod; last first.
      apply (@leZ_trans (2 ^^ (l - k) * 2 ^^ k)).
      rewrite -ZpowerD subnK //.
      exact: expZ_ge0.
      exact/ltnW/ltP.
      apply leZ_pmul2r => //; exact: expZ_gt0.
    apply u2Z_shl_Zmod; exact/ltP.
Qed.

Lemma shrl_2 : forall (v : int 32) z, u2Z v = 4 * z -> v `>> 2 = Z2u 32 z.
Proof.
move=> v z Hv; apply u2Z_inj.
have -> : u2Z (v `>> 2) = z.
  apply (@eqZ_mul2l 4) => //.
  rewrite -Hv mulZC -(@u2Z_shrl _ v 2); last by repeat constructor.
  by rewrite (@u2Z_rem'' _ _ _ z) //= addZ0.
rewrite Z2uK //.
split.
- move: (min_u2Z v) => ?; omega.
- apply (@ltZ_trans (2 ^^ 30)); last by [].
  move: (max_u2Z v); rewrite (_ : 2 ^^ 32 = 2 ^^ 30 * 4) // Hv mulZC.
  move/Zmult_gt_0_lt_reg_r; by apply.
Qed.

Lemma u2Z_shrl' n (x : int n) k : (n >= k)%nat ->  u2Z (x `>> k) = u2Z x / 2 ^^ k.
Proof.
move=> n_k.
rewrite -(@u2Z_shrl _ x k) // addZC Z_div_plus; last exact/Z.lt_gt/expZ_gt0.
rewrite (_ : _ / _ = 0) // Zdiv_small //.
split; by [apply min_u2Z | apply max_u2Z].
Qed.

(* NB: experimental *)
Lemma u2Z_add_new :
  forall n (a b : int n) P,
    (u2Z a + u2Z b < 2 ^^ n)%Z ->
    (u2Z a + u2Z b < 2 ^^ n -> P (u2Z a + u2Z b))%Z ->
    P (u2Z (a `+ b)) .
Proof.
move=> n a b P H1 H2.
rewrite u2Z_add //.
by apply H2.
Qed.

Lemma s2Z_add_new :
  forall n (a b : int n.+1) P,
    (- 2 ^^ n <= s2Z a + s2Z b < 2 ^^ n)%Z ->
    (- 2 ^^ n <= s2Z a + s2Z b < 2 ^^ n -> P (s2Z a + s2Z b))%Z ->
    P (s2Z (a `+ b)) .
Proof.
move=> n a b P H1 H2.
rewrite s2Z_add //.
by apply H2.
Qed.

Lemma u2Z_Z2u_new : forall n (z : Z) P,
  0 <= z < 2 ^^ n ->
  (0 <= z < 2 ^^ n -> P z) ->
  P (u2Z (Z2u n z)).
Proof. move=> n z P H G. rewrite Z2uK //; by auto.
Qed.

Definition u2nat {n} (a : int n) : nat := Z.abs_nat (u2Z a).
Definition s2nat {n} (a: int n) := Z.abs_nat (s2Z a).

Notation "'nat<=u'" := (u2nat) (at level 9) : machine_int_scope.
Notation "'Z<=u'" := (u2Z) (at level 9) : machine_int_scope.
Notation "'nat<=s'" := (s2nat) (at level 9) : machine_int_scope.
Notation "'Z<=s'" := (s2Z) (at level 9) : machine_int_scope.
Notation "'u32<=Z'" := (Z2u 32) (at level 9) : machine_int_scope.

Unset Implicit Arguments.
Unset Strongly Strict Implicit.

(** Some constants: *)
Definition one5 := Z2u 5 1.
Definition two5 := Z2u 5 2.
Definition thirtyone5 := Z2u 5 31.
Definition zero16 := Z2u 16 0.
Definition one16 := Z2u 16 1.
Definition four16 := Z2u 16 4.
Definition mone16 := MachineInt.Z2s 16 (-1)%Z.
Definition mfour16 := Z2s 16 (-4)%Z.
Definition zero8 := Z2u 8 0.
Definition zero32 := Z2u 32 0.
Definition one32 := Z2u 32 1.
Definition four32 := Z2u 32 4.

Section IntEqType.

Variable sz: nat.

Definition eq_int (a b: int sz) : bool := u2Z a == u2Z b.

Lemma eq_intP : Equality.axiom eq_int.
Proof.
move=> x y; apply: (iffP idP) => [/eqP |->]; [exact/u2Z_inj | exact/eqP].
Qed.

Canonical int_eqMixin := EqMixin eq_intP.
Canonical int_eqType := Eval hnf in EqType _ int_eqMixin.

End IntEqType.

Definition nth' := nosimpl (@seq.nth).
Notation "l `_ i" := (nth' _ zero8 l i) (at level 3, i at level 2, left associativity) : machine_int_scope.
Notation "l `32_ i" := (nth' _ zero32 l i) (at level 3, i at level 2) : machine_int_scope.

Module Int32Order <: ORDER.

Definition A := int_eqType 32.

Definition ltA : A -> A -> bool := @lt_n 32%nat.

Lemma ltA_trans : forall n m p, ltA m n -> ltA n p -> ltA m p.
Proof.
move=> n m p /lt_n2Zlt n_m /lt_n2Zlt n_p.
exact/Zlt2lt_n/(ltZ_trans n_m n_p).
Qed.

Lemma ltA_total m n : (m != n) = (ltA m n) || (ltA n m).
Proof.
case: (Ztrichotomy_inf (u2Z m) (u2Z n)).
- case=> m_n.
  + apply/negP/orP.
    * move=> _; left; exact: Zlt2lt_n.
    * case; move/lt_n2Zlt.
      - move/ltZ_eqF => m_n' /eqP ?; by subst m.
      - by move/(ltZ_trans m_n)/ltZZ.
  + move/u2Z_inj : m_n => m_n; subst m.
    apply/negP/orP => //.
    move=> X.
    move: (@lt_n_irrefl 32%nat n); tauto.
- move=> m_n.
  + apply/negP/orP.
    * move=> _; right.
      exact/Zlt2lt_n/Zgt_lt.
    * case=> [ _ | n_m].
      - apply/negP.
        move/Zgt_lt : m_n => /ltZ_eqF/eqP.
        by apply contra => /eqP ->.
      - apply/negP.
        move/lt_n2Zlt : n_m => /gtZ_eqF/eqP.
        by apply contra => /eqP ->.
Qed.

Lemma ltA_irr a : ltA a a = false.
Proof. rewrite /ltA; by move/negP/negbTE: (@lt_n_irrefl _ a) => ->. Qed.

End Int32Order.

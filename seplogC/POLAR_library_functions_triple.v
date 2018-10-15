(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import fintype tuple.
Require Import ssrZ ZArith_ext String_ext.
From mathcomp Require Import seq.
Require Import seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_expr_equiv.
Require Import POLAR_ssl_ctxt POLAR_library_functions.
Require Import rfc5246.
Import RFC5932.
Require Import POLAR_parse_client_hello_header.

Definition SSL_BUFFER_LEN : Z := (16384 + 512)%Z.

Local Open Scope C_types_scope.
Local Open Scope string_scope.
Local Open Scope machine_int_scope.
Local Open Scope seq_ext_scope.
Local Open Scope POLAR_scope.
Local Open Scope zarith_ext_scope.

Lemma ssl_fetch_input_triple (n : nat) (in_left0 : int 32)
  (SI BU : seq (int 8)) (majv0 minv0 mmaj0 mmin0 : int 32)
  (a rb : (:* (g.-ityp: uchar)).-phy)
  (ses : (:* (g.-typ: styp (mkTag _ssl_session))).-phy)
  (ciphers : (:* (g.-ityp: sint)).-phy)
  (md5s sha1s : 5.-tuple (int ptr_len))
  (ret : string)
  (Hret: env_get ret sigma = Some (g.-ityp: sint))
  (nexp : exp sigma (g.-ityp: sint)):
  let Ha_init := [ a ]c |---> map phy<=ui8 BU in
  let Hssl_init := Ssl_context (zext 24 S74.client_hello) majv0 minv0 mmaj0
    mmin0 ses a in_left0 md5s sha1s ciphers rb in
  let Hin_left0_init := !!(Z_of_nat n < SSL_BUFFER_LEN)%Z in
  let Hnexp_init := `! \b nexp \= [ Z_of_nat n]sc in
  let vret := @var_e g sigma ret _ Hret in
  let Herror := `! \~b \b vret \= [ 0 ]sc in
  let Hin_left_success_final := sepex in_left, Ssl_context
    (zext 24 S74.client_hello) majv0 minv0 mmaj0 mmin0 ses a in_left md5s sha1s
    ciphers rb ** !!( in_left = Z2u 32 (Z_of_nat n)) in
  let Hsuccess := `! \b vret \= [ 0 ]sc in
  let Ha_success_final := sepex BU',
    [ a ]c |---> map phy<=ui8 BU' **
      !!( BU' |{ 8 + '|u2Z in_left0| , n - '|u2Z in_left0|) =
          SI |{ '|u2Z in_left0|, n - '|u2Z in_left0|) ) **
      !!( BU' |{ 8, '|u2Z in_left0|) = BU |{ 8, '|u2Z in_left0|) ) **
      !!( size BU' = size BU) in
  let HSI_final := !!(n <= size SI)%nat in
  {{ Ha_init ** Hssl_init ** Hnexp_init ** Hin_left0_init }}
  ssl_fetch_input Logic.eq_refl ret Hret (%_ssl) nexp
  {{ (Hsuccess ** HSI_final ** Hin_left_success_final ** Ha_success_final)
     \\//
     (Herror ** TT) }}.
Admitted.

Lemma ssl_fetch_input_inde ret (H : env_get ret sigma = Some (g.-ityp: sint))
  (nexp : exp sigma (g.-ityp: sint)) :
  modified_vars (ssl_fetch_input Logic.eq_refl ret H (%_ssl) nexp) =
  (ret, g.-ityp: sint) :: nil.
Admitted.

Lemma memset_triple str H (ptr : exp sigma (:* (ityp: uchar)))
  (cst : exp sigma (ityp: sint)) sz count FROM (bytecst : (g.-ityp: uchar).-phy) :
  size FROM = count ->
  {{ `! \b cst \= [ (phyint) bytecst ]c **
     `! \b sz \= [ Z<=nat count ]uc ** ptr |---> FROM }}
  memset str H ptr cst sz
  {{ `! \b cst \= [ (phyint) bytecst ]c **
     `! \b sz \= [ Z<=nat count ]uc ** ptr |---> nseq count bytecst }}.
Admitted.

Lemma memset_input_inde str H ptr cst sz :
  modified_vars (memset str H ptr cst sz) = nil.
Admitted.

Lemma memset_triple_cst_e str (H : env_get str sigma = Some void_p )
  (ptr : exp sigma (:* (ityp: uchar)))
  (bytecst : (g.-ityp: uchar).-phy) count FROM :
  size FROM = count ->
  {{ ptr |---> FROM }}
  memset str H ptr [ (phyint) bytecst ]c [ Z<=nat count ]uc
  {{ ptr |---> nseq count bytecst }}.
Proof.
move=> HFROM.
do 2 rewrite -[X in {{ X }} _ {{ _ }}](coneP _).
do 2 rewrite -[X in {{ _ }} _ {{ X }}](coneP _).
rewrite -{1 3}bbang1.
rewrite -(beq_exx _ _ _ [ (phyint) bytecst ]c).
rewrite -{1 2}bbang1.
rewrite -(beq_exx _ _ _ [ Z<=nat count ]uc).
by apply memset_triple.
Qed.

Lemma memcpy_triple ret H e dest src len DEST SRC :
  Z<=nat (size SRC) = Z<=u len -> Z<=nat (size DEST) = Z<=u len ->
  {{ `! \b e \= [ len ]pc ** src |---> SRC ** dest |---> DEST }}
  memcpy ret H dest src e
  {{ `! \b e \= [ len ]pc ** src |---> SRC ** dest |---> SRC }}.
Admitted.

Lemma memcpy_input_inde ret H dest src len :
  modified_vars (memcpy ret H dest src len) = nil.
Admitted.

Local Open Scope zarith_ext_scope.

Lemma memcpy_triple_cst_e
  ret (Hret : env_get ret sigma = Some (:* (ityp: uchar)))
  (vret_e from_e : exp sigma (:* (ityp: uchar)))
  count (Hcount : 0 <= count < 2 ^^ ptr_len) RET FROM :
  Z<=nat (size FROM) = count ->
  Z<=nat (size RET) = count ->
  {{ from_e |---> FROM ** vret_e |---> RET }}
  @memcpy ret Hret vret_e from_e ([ count ]uc : exp sigma (ityp: uint))
  {{ from_e |---> FROM ** vret_e |---> FROM }}.
Proof.
move=>HFROM HRET.
rewrite -(coneP (_ ** _)) -[X in {{ _ }} _ {{ X }}](coneP (_ ** _)).
rewrite -bbang1 -(beq_exx _ _ _ [ `( count )_32 ]pc).
apply memcpy_triple => //; by rewrite Z2uK.
Qed.

(* TODO *)
Lemma md5_update_triple
  (Hmd5 : cover g (ptyp md5_context))
  (e0 : exp sigma (Ctyp.mk g _ Hmd5))
  (e1 : exp sigma void_p)
  (e2 : exp sigma (g.-ityp: sint)) :
  {{ FF }} md5_update Hmd5 e0 e1 e2 {{ TT }}.
Admitted.

(* TODO *)
Lemma sha1_update_triple
  (Hsha1 : cover g (ptyp sha1_context))
  (e0 : exp sigma (Ctyp.mk g _ Hsha1))
  (e1 : exp sigma void_p)
  (e2 : exp sigma (g.-ityp: sint)) :
  {{ FF }} sha1_update Hsha1 e0 e1 e2 {{ TT }}.
Admitted.

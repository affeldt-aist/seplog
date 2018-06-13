(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext String_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_seplog.

Local Open Scope C_types_scope.
Local Open Scope heap_scope.
Local Open Scope string_scope.

(** * PolarSSL Data Structures *)

(**
<<
struct _ssl_session {
    int cipher;                 /*!< chosen cipher      */
    int length;                 /*!< session id length  */
    unsigned char id[32];       /*!< session identifier */
    // ...
};
typedef struct _ssl_session ssl_session;
>>
*)

Definition _ssl_session := "ssl_session".
Definition _cipher := "cipher".
Definition _length := "length".
Definition _id := "id".

Definition ssl_sess :=
  ((_cipher, ityp sint) ::
   (_length, ityp sint) ::
   (_id,     ptyp (ityp uchar)) :: nil).
Definition ssl_session := styp (mkTag _ssl_session).

(**
<<
typedef struct
{
    unsigned long total[2];     /*!< number of bytes processed  */
    unsigned long state[4];     /*!< intermediate digest state  */
    unsigned char buffer[64];   /*!< data block being processed */

    unsigned char ipad[64];     /*!< HMAC: inner padding        */
    unsigned char opad[64];     /*!< HMAC: outer padding        */
}
md5_context;
>>
*)

Definition _md5_context := "md5_context".
Definition _total := "total".
Definition _state := "state".
Definition _buffer := "buffer".
Definition _ipad := "ipad".
Definition _opad := "opad".

Definition md5_cont :=
 ((_total, ptyp (ityp ulong)) ::
  (_state, ptyp (ityp ulong)) ::
  (_buffer, ptyp (ityp uchar)) ::
  (_ipad, ptyp (ityp uchar)) ::
  (_opad, ptyp (ityp uchar)) :: nil).
Definition md5_context := styp (mkTag _md5_context).

(**
typedef struct
{
    unsigned long total[2];     /*!< number of bytes processed  */
    unsigned long state[5];     /*!< intermediate digest state  */
    unsigned char buffer[64];   /*!< data block being processed */

    unsigned char ipad[64];     /*!< HMAC: inner padding        */
    unsigned char opad[64];     /*!< HMAC: outer padding        */
}
sha1_context;
*)

Definition _sha1_context := "sha1_context".

Definition sha1_cont :=
 ((_total, ptyp (ityp ulong)) ::
  (_state, ptyp (ityp ulong)) ::
  (_buffer, ptyp (ityp uchar)) ::
  (_ipad, ptyp (ityp uchar)) ::
  (_opad, ptyp (ityp uchar)) :: nil).
Definition sha1_context := styp (mkTag _sha1_context).

(**
<<
struct _ssl_context {
  /*
   * Miscellaneous
   */
  int state;                  /*!< SSL handshake: current state     */

  int major_ver;              /*!< equal to  SSL_MAJOR_VERSION_3    */
  int minor_ver;              /*!< either 0 (SSL3) or 1 (TLS1.0)    */

  int max_major_ver;          /*!< max. major version from client   */
  int max_minor_ver;          /*!< max. minor version from client   */

  /*
   * Callbacks (RNG, debug, I/O)
   */
  // int ( *f_recv)(void *, unsigned char *, int);

  // void *p_recv;               /*!< context for reading operations   */

  /*
   * Session layer
   */
   ssl_session *session;               /*!<  current session data    */

  /*
   * Record layer (incoming data)
   */
  unsigned char *in_hdr;      /*!< 5-byte record header (in_ctr+8)  */
  unsigned char *in_msg;      /*!< the message contents (in_hdr+5)  */

  int in_left;                /*!< amount of data read so far       */

  /*
   * Crypto layer
   */
  int *ciphers;                       /*!<  allowed ciphersuites    */

  unsigned char randbytes[64];        /*!<  random bytes            */

  // ...
}
typedef _ssl_context ssl_context;
>>
*)

Definition _ssl_context := "ssl_context".
Definition _major_ver := "major_ver".
Definition _minor_ver := "minor_ver".
Definition _max_major_ver := "max_major_ver".
Definition _max_minor_ver := "max_minor_ver".
Definition _session := "session".
Definition _in_hdr := "in_hdr".
Definition _in_msg := "in_msg".
Definition _in_left := "in_left".
Definition _fin_md5 := "fin_md5".
Definition _fin_sha1 := "fin_sha1".
Definition _ciphers := "ciphers".
Definition _randbytes := "randbytes".

Definition ssl_ctxt :=
((_state,         ityp sint) ::
 (_major_ver,     ityp sint) ::
 (_minor_ver,     ityp sint) ::
 (_max_major_ver, ityp sint) ::
 (_max_minor_ver, ityp sint) ::
 (_session,       ptyp ssl_session) ::
 (_in_hdr,        ptyp (ityp uchar)) ::
 (_in_msg,        ptyp (ityp uchar)) ::
 (_in_left,       ityp sint) ::
 (_fin_md5,       md5_context) ::
 (_fin_sha1,      sha1_context) ::
 (_ciphers,       ptyp (ityp sint)) ::
 (_randbytes,     ptyp (ityp uchar)) :: nil ).
Definition ssl_context := styp (mkTag _ssl_context).

Definition g :=
( \wfctxt{ _ssl_context |> ssl_ctxt \,
  _ssl_session |> ssl_sess\, _md5_context |> md5_cont\,
  _sha1_context |> sha1_cont\, \O \} ).

From mathcomp Require Import fintype tuple.

Definition inter1_lst (x : 5.-tuple (int ptr_len) ) : logs (get_fields g (mkTag _md5_context)) :=
cons_logs (_total, :* (ityp: ulong)) _
  (log_of_ptr _ (ityp: ulong) erefl (tnth x ord0))
  (cons_logs (_state, Ctyp.mk g (ptyp (ityp ulong)) erefl) _
    (log_of_ptr _ (ityp: ulong) erefl (tnth x (@Ordinal 5 1 erefl)))
    (cons_logs (_buffer, Ctyp.mk g (ptyp (ityp uchar)) erefl) _
      (log_of_ptr _ (ityp: uchar) erefl (tnth x (@Ordinal 5 2 erefl)))
      (cons_logs (_ipad, Ctyp.mk g (ptyp (ityp uchar)) erefl) _
        (log_of_ptr _ (ityp: uchar) erefl (tnth x (@Ordinal 5 3 erefl)))
        (cons_logs (_opad, Ctyp.mk g (ptyp (ityp uchar)) erefl) _
          (log_of_ptr _ (ityp: uchar) erefl (tnth x (@Ordinal 5 4 erefl)))
          nil_logs)))).

Definition inter2_lst (sha1s : 5.-tuple (int ptr_len) ) :
  logs (get_fields g (mkTag _sha1_context)) :=
cons_logs (_total, :* (ityp: ulong)) _
  (log_of_ptr _ (ityp: ulong) erefl (tnth sha1s (@Ordinal 5 0 erefl)))
  (cons_logs (_state, Ctyp.mk g (ptyp (ityp ulong)) erefl) _
    (log_of_ptr _ (ityp: ulong) erefl (tnth sha1s (@Ordinal 5 1 erefl)))
    (cons_logs (_buffer, Ctyp.mk g (ptyp (ityp uchar)) erefl) _
      (log_of_ptr _ (ityp: uchar) erefl (tnth sha1s (@Ordinal 5 2 erefl)))
      (cons_logs (_ipad, Ctyp.mk g (ptyp (ityp uchar)) erefl) _
        (log_of_ptr _ (ityp: uchar) erefl (tnth sha1s (@Ordinal 5 3 erefl)))
        (cons_logs (_opad, Ctyp.mk g (ptyp (ityp uchar)) erefl) _
          (log_of_ptr _ (ityp: uchar) erefl (tnth sha1s (@Ordinal 5 4 erefl)))
nil_logs)))).

Definition mk_ssl_ctxt_logs (state major_ver minor_ver max_major_ver max_minor_ver : int 32)
  (session in_hdr in_msg : int ptr_len) (in_left : int 32)
  (md5s sha1s : 5.-tuple (int ptr_len))
  (ciphers randbytes : int ptr_len) :
  logs ((_state, ityp: sint) ::
        (_major_ver, ityp: sint) ::
        (_minor_ver, ityp: sint) ::
        (_max_major_ver, ityp: sint) ::
        (_max_minor_ver, ityp: sint) ::
        (_session, :* (g.-typ: ssl_session)) ::
        (_in_hdr, :* (ityp: uchar)) ::
        (_in_msg, :* (ityp: uchar)) ::
        (_in_left, ityp: sint) ::
        (_fin_md5, g.-typ: md5_context) ::
        (_fin_sha1, g.-typ: sha1_context) ::
        (_ciphers, :* (ityp: sint)) ::
        (_randbytes, :* (ityp: uchar)) :: nil).
apply cons_logs.
  apply log_of_sint.
  reflexivity.
  exact state.
apply cons_logs.
  apply log_of_sint.
  reflexivity.
  exact major_ver.
apply cons_logs.
  apply log_of_sint.
  reflexivity.
  exact minor_ver.
apply cons_logs.
  apply log_of_sint.
  reflexivity.
  exact max_major_ver.
apply cons_logs.
  apply log_of_sint.
  reflexivity.
  exact max_minor_ver.
apply cons_logs.
  apply log_of_ptr with (g.-typ: ssl_session).
  reflexivity.
  exact session.
apply cons_logs.
  apply log_of_ptr with (ityp: uchar).
  reflexivity.
  exact in_hdr.
apply cons_logs.
  apply log_of_ptr with (ityp: uchar).
  reflexivity.
  exact in_msg.
apply cons_logs.
  apply log_of_sint.
  reflexivity.
  exact in_left.
apply cons_logs.
  apply (log_of_styp (g.-typ: md5_context) (mkTag _md5_context) Logic.eq_refl).
  exact (inter1_lst md5s).
apply cons_logs.
  apply (log_of_styp (g.-typ: sha1_context) (mkTag _sha1_context) Logic.eq_refl).
  exact (inter2_lst sha1s).
apply cons_logs.
  apply log_of_ptr with (ityp: sint).
  reflexivity.
  exact ciphers.
apply cons_logs.
  apply log_of_ptr with (ityp: uchar).
  reflexivity.
  exact randbytes.
exact nil_logs.
Defined.

Definition mk_ssl_context (state major_ver minor_ver max_major_ver max_minor_ver : int 32)
  (session : int ptr_len) (in_hdr in_msg : int ptr_len) (in_left : int 32)
  (md5s sha1s : 5.-tuple (int ptr_len)) (ciphers randbytes : int ptr_len) :
  log (g.-typ: ssl_context) :=
  log_of_styp (g.-typ: ssl_context) (mkTag _ssl_context) erefl
           (mk_ssl_ctxt_logs state major_ver minor_ver max_major_ver max_minor_ver
            session in_hdr in_msg in_left md5s sha1s ciphers randbytes).

Definition mk_ssl_sess_logs (cipher length : int 32) (id : int ptr_len) :
  logs ((_cipher, ityp: sint) :: (_length, ityp: sint) :: (_id, :* (g.-ityp: uchar)) :: nil).
apply cons_logs.
apply log_of_sint.
  reflexivity.
  exact cipher.
apply cons_logs.
  apply log_of_sint.
  reflexivity.
  exact length.
apply cons_logs.
  apply log_of_ptr with (t' := ityp: uchar).
  reflexivity.
  exact id.
by apply nil_logs.
Defined.

Definition mk_ssl_session (cipher length : int 32) (id : int ptr_len) :
  log (g.-typ: ssl_session) := log_of_styp (g .-typ: ssl_session) (mkTag _ssl_session)
  erefl (mk_ssl_sess_logs cipher length id).

Require Import seq_ext.

Section values_get_helper.

Variables state major_ver minor_ver max_major_ver max_minor_ver : int 32.
Variables session in_hdr in_msg : int ptr_len.
Variable in_left : int 32.
Variables md5s sha1s : 5.-tuple (int ptr_len).
Variables ciphers randbytes : int ptr_len.

Let ssl_ctxt_logs :=
  mk_ssl_ctxt_logs state major_ver minor_ver max_major_ver max_minor_ver
                   session in_hdr in_msg in_left md5s sha1s ciphers randbytes.

Lemma get_state_ssl_ctxt H :
  values_get _state _ (get_fields g (mkTag _ssl_context))
             ssl_ctxt_logs (assoc_get_in H) =
  log_of_sint (g.-ityp: sint) erefl state.
Proof.
simpl.
symmetry.
by apply Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

Lemma get_in_left_ssl_ctxt H :
  values_get _in_left _ (get_fields g (mkTag _ssl_context))
             ssl_ctxt_logs (assoc_get_in H) =
  log_of_sint (g.-ityp: sint) erefl in_left.
Proof.
simpl.
symmetry.
by apply Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

Lemma get_in_hdr_ssl_ctxt H :
  values_get _in_hdr _ (get_fields g (mkTag _ssl_context))
             ssl_ctxt_logs (assoc_get_in H) =
  log_of_ptr _ (ityp: uchar) erefl in_hdr.
Proof.
simpl.
symmetry.
by apply Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

Lemma get_in_msg_ssl_ctxt H :
  values_get _in_msg _ (get_fields g (mkTag _ssl_context))
             ssl_ctxt_logs (assoc_get_in H) =
  log_of_ptr _ (ityp: uchar) erefl in_msg.
Proof.
simpl.
symmetry.
by apply Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

Lemma get_randbytes_ssl_ctxt H :
  values_get _randbytes _ (get_fields g (mkTag _ssl_context))
             ssl_ctxt_logs (assoc_get_in H) =
  log_of_ptr _ (ityp: uchar) erefl randbytes.
Proof.
simpl.
symmetry.
by apply Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

Lemma get_session_ssl_ctxt H :
  values_get _session _ (get_fields g (mkTag _ssl_context))
             ssl_ctxt_logs (assoc_get_in H) =
  log_of_ptr _ (g.-typ: ssl_session) erefl session.
Proof.
simpl.
symmetry.
by apply Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

Lemma get_ciphers_ssl_ctxt H :
  values_get _ciphers _ (get_fields g (mkTag _ssl_context))
             ssl_ctxt_logs (assoc_get_in H) =
  log_of_ptr _ (ityp: sint) erefl ciphers.
Proof.
simpl.
symmetry.
by apply Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
Qed.

End values_get_helper.

Lemma cons_logs_f_equal2 g h t H1 H2 H2' : H2 = H2' ->
  @cons_logs g h t H1 H2 = cons_logs h t H1 H2'.
Proof. by move=> ->. Qed.

Lemma cons_logs_f_equal1 g h t H1 H1' H2 : H1 = H1' ->
  @cons_logs g h t H1 H2 = cons_logs h t H1' H2.
Proof. by move=> ->. Qed.

Section values_set_helper.

Variables state major_ver minor_ver max_major_ver max_minor_ver : int 32.
Variables session in_hdr in_msg : int ptr_len.
Variable in_left : int 32.
Variables md5s sha1s : 5.-tuple (int ptr_len).
Variables ciphers randbytes : int ptr_len.

Let ssl_ctxt_logs :=
  mk_ssl_ctxt_logs state major_ver minor_ver max_major_ver max_minor_ver
                   session in_hdr in_msg in_left md5s sha1s ciphers randbytes.

Lemma set_state_ssl_ctxt v H H1 :
  values_set  _state _ (log_of_sint (g.-ityp: sint) H v)
    (get_fields g (mkTag _ssl_context)) ssl_ctxt_logs (assoc_get_in H1) =
  mk_ssl_ctxt_logs v major_ver minor_ver max_major_ver max_minor_ver
                   session in_hdr in_msg in_left
                   md5s sha1s
                   ciphers randbytes.
Proof.
simpl.
apply cons_logs_f_equal1.
rewrite -Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
congr log_of_sint.
by apply eq_irrelevance.
Qed.

Lemma set_major_ver_ssl_ctxt v H H1 :
  values_set _major_ver _  (log_of_sint (g.-ityp: sint) H v)
    (get_fields g (mkTag _ssl_context)) ssl_ctxt_logs (assoc_get_in H1) =
  mk_ssl_ctxt_logs state v minor_ver max_major_ver max_minor_ver
                   session in_hdr in_msg in_left
                   md5s sha1s
                   ciphers randbytes.
Proof.
simpl.
apply cons_logs_f_equal2.
apply cons_logs_f_equal1.
rewrite -Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
congr log_of_sint.
by apply eq_irrelevance.
Qed.

Lemma set_minor_ver_ssl_ctxt v H H1 :
  values_set _minor_ver _ (log_of_sint (g.-ityp: sint) H v)
    (get_fields g (mkTag _ssl_context)) ssl_ctxt_logs (assoc_get_in H1) =
  mk_ssl_ctxt_logs state major_ver v max_major_ver max_minor_ver
                   session in_hdr in_msg in_left md5s sha1s
                   ciphers randbytes.
Proof.
simpl.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal1.
rewrite -Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
congr log_of_sint.
by apply eq_irrelevance.
Qed.

Lemma set_max_major_ver_sl_ctxt v H H1 :
  values_set _max_major_ver _ (log_of_sint (g.-ityp: sint) H v)
    (get_fields g (mkTag _ssl_context)) ssl_ctxt_logs (assoc_get_in H1) =
  mk_ssl_ctxt_logs state major_ver minor_ver v max_minor_ver
                   session in_hdr in_msg in_left md5s sha1s
                   ciphers randbytes.
Proof.
simpl.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal1.
rewrite -Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
congr log_of_sint.
by apply eq_irrelevance.
Qed.

Lemma set_max_minor_ver_ssl_ctxt v H H1 :
  values_set _max_minor_ver _ (log_of_sint (g.-ityp: sint) H v)
    (get_fields g (mkTag _ssl_context)) ssl_ctxt_logs (assoc_get_in H1) =
  mk_ssl_ctxt_logs state major_ver minor_ver max_major_ver v
        session in_hdr in_msg in_left md5s sha1s
        ciphers randbytes.
Proof.
simpl.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal1.
rewrite -Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
congr log_of_sint.
by apply eq_irrelevance.
Qed.

Lemma set_in_left_ssl_ctxt v H H1 :
  values_set _in_left _ (log_of_sint (g.-ityp: sint) H v)
    (get_fields g (mkTag _ssl_context)) ssl_ctxt_logs (assoc_get_in H1) =
  mk_ssl_ctxt_logs state major_ver minor_ver max_major_ver max_minor_ver
                   session in_hdr in_msg v md5s sha1s
                   ciphers randbytes.
Proof.
simpl.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal2.
apply cons_logs_f_equal1.
rewrite -Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
congr log_of_sint.
by apply eq_irrelevance.
Qed.

End values_set_helper.

Definition _ret := "ret".
Definition _ssl := "ssl".
Definition _buf := "buf".
Definition _buf0 := "_buf0_".
Definition _buf1 := "_buf1_".
Definition _buf2 := "_buf2_".
Definition _buf3 := "_buf3_".
Definition _buf4 := "_buf4_".
Definition _buf5 := "_buf5_".
Definition _buf38' := "_buf38'_".
Definition _buf38 := "_buf38_".
Definition _n := "n".
Definition _n_old := "n_old". (* PATCH *)
Definition _n0 := "_n0_".
Definition _it := "_it_".
Definition _sess_len := "sess_len".
Definition _ssl_session_0 := "_ssl_session_0_".
Definition _ssl_session_0_length := "_ssl_session_0_length_".
Definition _buf39_plus_sess_len := "_buf39_plus_sess_len_".
Definition _buf40_plus_sess_len := "_buf40_plus_sess_len_".
Definition _ciph_len := "ciph_len".
Definition _comp_len := "comp_len".
Definition _comp_len' := "comp_len'".
Definition _goto_have_cipher := "_goto_have_cipher_".
Definition _i := "i".
Definition _ssl_ciphers := "_ssl_ciphers_".
Definition _ssl_ciphers_i := "_ssl_ciphers_i_".
Definition _j := "j".
Definition _p := "p".
Definition _p0 := "_p0_".
Definition _p1 := "_p1_".
Definition _ssl_state := "_ssl_state_".

Definition sigma : g.-env :=
 (_ret, ityp: sint) ::
 (_ssl, :* (g.-typ: ssl_context)) ::
 (_buf, :* (ityp: uchar)) ::
 (_buf0, ityp: uchar) ::
 (_buf1, ityp: uchar) ::
 (_buf2, ityp: uchar) ::
 (_buf3, ityp: uchar) ::
 (_buf4, ityp: uchar) ::
 (_buf5, ityp: uchar) ::
 (_buf38', :* (ityp: uchar)) ::
 (_buf38, ityp: uchar) ::
 (_n, ityp: sint) ::
 (_n_old, ityp: sint) :: (* PATCH *)
 (_n0, ityp: sint) ::
 (_it, :* (ityp: uchar)) ::
 (_sess_len, ityp: sint) ::
 (_ssl_session_0, :* (g.-typ: ssl_session)) ::
 (_ssl_session_0_length, ityp: sint) ::
 (_buf39_plus_sess_len, ityp: uchar) ::
 (_buf40_plus_sess_len, ityp: uchar) ::
 (_ciph_len, ityp: sint) ::
 (_comp_len, ityp: sint) ::
 (_comp_len', ityp: uchar) ::
 (_goto_have_cipher, ityp: sint) ::
 (_i, ityp: sint) ::
 (_ssl_ciphers, :* (ityp: sint)) ::
 (_ssl_ciphers_i, ityp: sint) ::
 (_j, ityp: sint) ::
 (_p, :* (ityp: uchar)) ::
 (_p0, ityp: uchar) ::
 (_p1, ityp: uchar) ::
 (_ssl_state, ityp: sint) :: nil.

Time Eval compute in sizeof (g.-typ: ssl_context).

Module parse_client_env <: CENV.

Definition g := g.
Definition sigma : g.-env := sigma.
Definition uniq_vars : uniq (unzip1 sigma) := erefl.

End parse_client_env.

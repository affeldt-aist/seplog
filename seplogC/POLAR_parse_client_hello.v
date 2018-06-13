(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import ZArith_ext String_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_seplog.
Require Import POLAR_ssl_ctxt POLAR_library_functions.
From mathcomp Require Import fintype tuple.
Require Import rfc5246.
Import RFC5932.
From mathcomp Require Import seq.

Local Open Scope C_expr_scope.
Local Open Scope C_cmd_scope.
Local Open Scope C_types_scope.
Local Open Scope C_value_scope.
Local Open Scope string_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope multi_int_scope.

(** Macro Constants from PolarSSL: *)
Definition POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO : (g.-ityp: sint).-phy := [ -38912 ]s.
Definition POLARSSL_ERR_SSL_NO_CIPHER_CHOSEN    : (g.-ityp: sint).-phy := [ -16384 ]s.

(** from inlude/polarssl/ssl.h *)
Definition SSL_MAJOR_VERSION_3 : (g.-ityp: uchar).-phy := [ 3 ]u.
Definition SSL_MSG_HANDSHAKE   : (g.-ityp: uchar).-phy := [ 22 ]u.
Definition SSL_HS_CLIENT_HELLO : (g.-ityp: uchar).-phy := [ 1 ]u.
Definition SSL_MINOR_VERSION_2 : (g.-ityp: uchar).-phy := [ 2 ]u.

(** * The ClientHello Parsing Program *)

(** NB: ssl_parse_client_hello is called from ssl/server.v, main function,
   l.305 (ssl_handshake function) *)

Definition __ssl := nosimpl (%_ssl).
Definition __ret := nosimpl (%_ret).
Definition __buf := nosimpl (%_buf).
Definition __buf0 := nosimpl (%_buf0).
Definition __buf1 := nosimpl (%_buf1).
Definition __buf3 := nosimpl (%_buf3).
Definition __buf4 := nosimpl (%_buf4).
Definition __n := nosimpl (%_n).

Local Open Scope POLAR_scope.

(** NB: it has been tested by retrofitting the generated code to PolarSSL
    that the interpretation of return as skip is ok *)

Definition Return := skip.

(* NB: the ssl pointer is initialized in library/ssl_tls.c, function ssl_init, l.1680:
       memset( ssl, 0, sizeof( ssl_context ) ); *)
Definition ssl_parse_client_hello1 cont :=
  (** <<
     ssl_context *ssl;
     int ret, i, j, n;
     int sess_len;
     unsigned char *buf, *p;
     if( ( ret = ssl_fetch_input( ssl, 5 ) ) != 0 ) { return( ret ); } >> *)
  _ret <-ssl_fetch_input(__ssl, [ 5 ]sc) ;
  If \b __ret \!= [ 0 ]sc Then
    Return
  Else (
  (** << buf = ssl->in_hdr; >> *)
  _buf <-* __ssl &-> _in_hdr (*.=> get_in_hdr*) ;
  (** << if( ( buf[0] & 0x80 ) != 0 ) { ... } { ... } >> *)
  (* NB: this check is redundant with the next operation *)
  _buf0 <-* __buf ;
(* for decimal, it is the first type the value can fit in:
   int, long, long long
   for hexadecimal, it is the first type the value can fit in:
   int, unsigned int, long, unsigned long, etc.
   on a system with 32-bit int and unsigned int, 0x80000000 is unsigned int *)
  If \b (__buf0 \& [ 128 ]uc) \!= [ 0 ]uc Then
    (* --- client hello v2 message; we consider this case as an error --- *)
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c;
    Return
  Else ( (* --- SSLv3 Client Hello --- *)
  (** << if( buf[0] != SSL_MSG_HANDSHAKE || buf[1] != SSL_MAJOR_VERSION_3 )
      { return( POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ); } >> *)
  If \b __buf0 \!= [ SSL_MSG_HANDSHAKE ]c Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c ;
    Return
  Else (
  _buf1 <-* __buf \+ [ 1 ]sc ;
  If \b __buf1 \!= [ SSL_MAJOR_VERSION_3 ]c Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c ;
    Return
  Else (
  (** << n = ( buf[3] << 8 ) | buf[4]; >> *)
  _buf3 <-* __buf \+ [ 3 ]sc ;
  _buf4 <-* __buf \+ [ 4 ]sc ;
  _n <- (( (int) __buf3) \<< [ 8 ]sc) \| (int) __buf4 ;
  (** << if( n < 45 || n > 512 ) { return( POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ); } >> *)
  If \b __n \< [ 45 ]sc Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c;
    Return
  Else (
  If \b __n \> [ 512 ]sc Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c ;
    Return
  Else (
    cont)))))).

Definition __n0 := nosimpl (%_n0).
Definition __buf5 := nosimpl (%_buf5).
Definition __it := nosimpl (%_it).
Definition __n_old := nosimpl (%_n_old). (* PATCH *)

Definition ssl_parse_client_hello2 cont :=
  (** << if( ( ret = ssl_fetch_input( ssl, 5 + n ) ) != 0 ) { return( ret ); } >> *)
  _ret <-ssl_fetch_input(__ssl, [ 5 ]sc \+ __n) ;
  If \b __ret \!= [ 0 ]sc Then
    Return
  Else (
  (** << buf = ssl->in_msg; >> *)
  _buf <-* __ssl &-> _in_msg (*.=> get_in_msg*) ;
  (** << n = ssl->in_left - 5; >> *)
  _n0 <-* __ssl &-> _in_left (*.=> get_in_left*) ;
  _n_old <- __n ; (* PATCH *)
  _n <- __n0 \- [ 5 ]sc ;
  (** <<
      md5_update( &ssl->fin_md5 , buf, n );
      sha1_update( &ssl->fin_sha1, buf, n ); >> *)
  md5_update(__ssl &-> _fin_md5 (*.=> get_fin_md5*), __buf, __n) ;
  sha1_update(__ssl &-> _fin_sha1 (*.=> get_fin_sha1*) , __buf, __n) ;
  (** << if( buf[0] != SSL_HS_CLIENT_HELLO || buf[4] != SSL_MAJOR_VERSION_3 )
      { return( POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ); } >> *)
  _buf0 <-* __buf ;
  If \b __buf0 \!= [ SSL_HS_CLIENT_HELLO ]c Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c ;
    Return
  Else (
  _buf4 <-* __buf \+ [ 4 ]sc ;
  If \b __buf4 \!= [ SSL_MAJOR_VERSION_3 ]c Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c ;
    Return
  Else (
  (** << ssl->major_ver = SSL_MAJOR_VERSION_3; >> *)
  __ssl &-> _major_ver (*.=> get_major_ver*) *<- (int) ([ SSL_MAJOR_VERSION_3 ]c) (* NB: cast instead of preprocessing *) ;
  (** << ssl->minor_ver = (buf[5] <= SSL_MINOR_VERSION_2) ? buf[5] : SSL_MINOR_VERSION_2; >> *)
  _buf5 <-* __buf \+ [ 5 ]sc ;
  __ssl &-> _minor_ver (*.=> get_minor_ver*) *<- (int) (__buf5 \<= [ SSL_MINOR_VERSION_2 ]c \? __buf5 \: [ SSL_MINOR_VERSION_2 ]c) ;
  (** <<
      ssl->max_major_ver = buf[4];
      ssl->max_minor_ver = buf[5]; >> *)
  __ssl &-> _max_major_ver (*.=> get_max_major_ver*) *<- (int) __buf4 ;
  __ssl &-> _max_minor_ver (*.=> get_max_minor_ver*) *<- (int) __buf5 ;
  (* NB: store the nonce from ClientHello;
         for storage of the server's nonce, see library/ssl_srv.c,
         function ssl_write_server_hello, l.389:
         memcpy( ssl->rand
bytes + 32, buf + 6, 32); *)

  (** << memcpy( ssl->randbytes, buf + 6, 32 ); >> *)
  _it <-* __ssl &-> _randbytes (*.=> get_randbytes*) ;
  _it <-memcpy(__it, __buf \+ [ 6 ]sc, [ 32 ]uc) ;
  (** << if( buf[1] != 0 || n != 4 + ( ( buf[2] << 8 ) | buf[3] ) )
      { return( POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ); } >> *)
  _buf1 <-* __buf \+ [ 1 ]sc ;
  If \b __buf1 \!= [ 0 ]uc Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c ;
    Return
  Else (
  _buf2 <-* __buf \+ [ 2 ]sc ;
  _buf3 <-* __buf \+ [ 3 ]sc ;
  cont)))).

Definition __buf2 := nosimpl (%_buf2).
Definition __buf38 := nosimpl (%_buf38).
Definition __sess_len := nosimpl (%_sess_len).
Definition __ssl_session_0 := nosimpl (%_ssl_session_0).
Definition __ssl_session_0_length := nosimpl (%_ssl_session_0_length).
Definition __buf39_plus_sess_len := nosimpl (%_buf39_plus_sess_len).
Definition __buf40_plus_sess_len := nosimpl (%_buf40_plus_sess_len).
Definition __ciph_len := nosimpl (%_ciph_len).
Definition __comp_len' := nosimpl (%_comp_len').
Definition __comp_len := nosimpl (%_comp_len).

Definition ssl_parse_client_hello3 cont :=
  If \b __n \!= [ 4 ]sc \+ (( (int) __buf2 \<< [ 8 ]sc) \| (int) __buf3) Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c ;
    Return
  Else (
  (** << sess_len = buf[38]; >> *)
  _buf38 <-* __buf \+ [ 38 ]sc ;
  _sess_len <- (int) __buf38 ;
  (** << if( sess_len < 0 || sess_len > 32 )
      { return( POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ); } >> *)
  If \b ( __sess_len \< [ 0 ]sc \|| __sess_len \> [ 32 ]sc )
        \|| ( [ Z_of_nat 44(*csuites*).+1 ]sc \+ __sess_len \>= [ 5 ]sc \+ __n_old) (* PATCH1 *) Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c;
    Return
  Else
  (** <<
      ssl->session->length = sess_len;
      memset( ssl->session->id, 0, sizeof( ssl->session->id ) );
      // sizeof(ssl->session->id) == sizeof(typeof(unsigned char* ))
      memcpy( ssl->session->id, buf + 39 , ssl->session->length ); >> *)
  _ssl_session_0 <-* __ssl &-> _session (*.=> get_session*) ;
  (
  __ssl_session_0 &-> _length (*.=> get_length*) *<- __sess_len ;
  _it <-* __ssl_session_0 &-> _id (*.=> get_id*) ;
  _it <-memset(__it, [ 0 ]sc, [ 32 ]uc) ;
  _ssl_session_0_length <-* __ssl_session_0 &-> _length (*.=> get_length*) ;
  _it <-* __ssl_session_0 &-> _id (*.=> get_id*) ;
  _it <-memcpy(__it, __buf \+ [ 39 ]sc, ((UINT) __ssl_session_0_length) ) ;
 (** << ciph_len = ( buf[39 + sess_len] << 8 ) | ( buf[40 + sess_len]      ); >> *)
  _buf39_plus_sess_len <-* __buf \+ ([ 39 ]sc \+ __sess_len) ;
  _buf40_plus_sess_len <-* __buf \+ ([ 40 ]sc \+ __sess_len) ;
  _ciph_len <- ( (int) __buf39_plus_sess_len \<< [ 8 ]sc) \| ( (int) __buf40_plus_sess_len) ;
  (
  (** << if( ciph_len < 2 || ciph_len > 256 || ( ciph_len mod 2 ) != 0 )
         { return( POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ); } >> *)
  If \b (__ciph_len \< [ 2 ]sc \|| __ciph_len \> [ 256 ]sc \|| __ciph_len \% 1 \!= [ 0 ]sc)
        \|| ([ Z_of_nat 46(*compmeth*) ]sc \+ __sess_len \+ __ciph_len \>= [ 5 ]sc \+ __n_old) (* PATCH2 *) Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c ;
    Return
  Else (
  (** << comp_len = buf[41 + sess_len + ciph_len]; >> *)
  _comp_len' <-* __buf \+ ([ 41 ]sc \+ __sess_len \+ __ciph_len) ;
  _comp_len <- (int) __comp_len' ;
  (** << if( comp_len < 1 || comp_len > 16 )
      { return( POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ); } >> *)
  If \b (__comp_len \< [ 1 ]sc \|| __comp_len \> [ 16 ]sc)
      \|| ([ Z_of_nat 46(*compmeth*).+1 ]sc \+ __sess_len \+ __ciph_len \+ __comp_len \!= [ 5 ]sc \+ __n_old) (*PATCH3*) Then
    _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c ;
    Return
  Else (
  (** << for( i = 0; ssl->ciphers[i] != 0; i++ ) { ... } >> *)
  _goto_have_cipher <- [ 0 ]sc ;
  cont))))).

Definition __ssl_ciphers_i := nosimpl (%_ssl_ciphers_i).
Definition __ssl_ciphers := nosimpl (%_ssl_ciphers).
Definition __i := nosimpl (%_i).
Definition __goto_have_cipher := nosimpl (%_goto_have_cipher).
Definition __j := nosimpl (%_j).
Definition __p := nosimpl (%_p).
Definition __p0 := nosimpl (%_p0).
Definition __p1 := nosimpl (%_p1).
Definition __ssl_state := nosimpl (%_ssl_state).

Definition ssl_parse_client_hello4 cont : cmd :=
  For(_i <- [ 0 ]sc \;
      If \b __goto_have_cipher \= [ 0 ]sc Then
        _ssl_ciphers <-* __ssl &-> _ciphers (*.=> get_ciphers*); _ssl_ciphers_i <-* __ssl_ciphers \+ __i
      Else
         nop \,
      __goto_have_cipher \= [ 0 ]sc \&& __ssl_ciphers_i \!= [ 0 ]sc \;
      _i \++ ){{
    (** << for( j = 0, p = buf + 41 + sess_len; j < ciph_len; j += 2, p += 2 ) { ... } >> *)
    For(_j <- [ 0 ]sc ; _p <- __buf \+ [ 41 ]sc \+ __sess_len \;
        __goto_have_cipher \= [ 0 ]sc \&& __j \< __ciph_len \;
        nop ){{
      (** << if( p[0] == 0 && p[1] == ssl->ciphers[i] ) ... >> *)
      _p0 <-* __p ;
      If \b __p0 \= [ 0 ]uc Then
        _p1 <-* __p \+ [ 1 ]sc ;
      (* <<
        "_ssl_ciphers_" <-* %"ssl" .=> ciphers ;
        "_ssl_ciphers_i_" <-* %"_ssl_ciphers_" \+ %"i" ; >> *)
        If \b (int) __p1 \= __ssl_ciphers_i Then
          (** goto have_cipher; *)
          _goto_have_cipher <- [ 1 ]sc
        Else
          _j \+<- [ 2 ]sc ;
          _p \+<- [ 2 ]sc
      Else
        _j \+<- [ 2 ]sc ;
        _p \+<- [ 2 ]sc
      }}
  }} ; cont.

Definition ssl_parse_client_hello5 :=
  If \b __goto_have_cipher \!= [ 0 ]sc Then
    (** <<
        ssl->session->cipher = ssl->ciphers[i];
        ssl->in_left = 0;
        ssl->state++;
        return( 0 ); >> *)
    __ssl_session_0 &-> _cipher (*.=> get_cipher*) *<- __ssl_ciphers_i ;
    __ssl &-> _in_left (*.=> get_in_left*) *<- [ 0 ]sc ;
    _ssl_state <-* __ssl &-> _state (*.=> get_state*) ;
    __ssl &-> _state (*.=> get_state*) *<- __ssl_state \+ [ 1 ]sc ;
    _ret <- [ 0 ]sc ;
    Return
  Else
   (** << return( POLARSSL_ERR_SSL_NO_CIPHER_CHOSEN ); >> *)
    _ret <- [ POLARSSL_ERR_SSL_NO_CIPHER_CHOSEN ]c ;
    Return.

Definition ssl_parse_client_hello :=
  ssl_parse_client_hello1
 (ssl_parse_client_hello2
 (ssl_parse_client_hello3
 (ssl_parse_client_hello4
  ssl_parse_client_hello5))).

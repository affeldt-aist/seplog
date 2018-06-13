(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Div2 Even.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ZArith_ext String_ext ssrZ seq_ext.
Require Import multi_int machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_expr C_expr_equiv C_expr C_expr_ground C_seplog C_tactics C_value.
Require Import POLAR_ssl_ctxt POLAR_library_functions POLAR_parse_client_hello (* where the variables are defined *).
Require Import rfc5246.
Import RFC5932.

Local Open Scope zarith_ext_scope.
Local Open Scope seq_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope C_types_scope.
Local Open Scope C_expr_scope.
Local Open Scope C_cmd_scope.

(** * Various Constants Used to Parse ClientHello Packets *)

Definition record_flag := O.

(** indices for major/minor versions in the Record header *)
Definition maj_ver := (* 1 *) '| fixed_sz S621.ContentType |.
Definition min_ver := (* 2 *) (maj_ver + '| fixed_sz S44.uint8 |)%nat.

(** length of the payload of the Record: starting index and length itself *)
Definition record_sz := (* 3 *) '| fixed_sz S621.ContentType + fixed_sz S621.ProtocolVersion |.
Definition n' A := A `_ record_sz :: A `_ record_sz.+1 :: nil.
Definition n A := '| bSum_c 8 (n' A) |.

Definition handshake_flag := '| (S74.Handshake_hd + 1) |.

(** length of the payload of the Handshake: starting index and length itself *)
Definition handshake_sz := (* 6 *) '| S621.TLSPlainText_hd + fixed_sz S621.ContentType |.
Definition m' A := A `_ handshake_sz :: A `_ handshake_sz.+1 :: A `_ handshake_sz.+2 :: nil.
Definition m A := '| bSum_c 8 (m' A) |.

(** indices of the requested major/minor version by the client *)
Definition maj_req := (* 9 *) '| S621.TLSPlainText_hd + S74.Handshake_hd |.
Definition min_req := (* 10 *) (maj_req + '| fixed_sz S44.uint8 |)%nat.

(** starting index of the client's random bytes *)
Definition rand := (* 11 *) '| S621.TLSPlainText_hd + S74.Handshake_hd +
  fixed_sz S621.ProtocolVersion |.

(** length of client's SessionID: starting index and length itself *)
Definition sid := (* 43 *) (rand + '| fixed_sz S7412.Random |)%nat.
Definition sess_len A := nat<=u (A `_ sid).

(** total length of cipher suites: smallest possible index and length itself *)
Definition csuites := (* 44 *) '| S621.TLSPlainText_hd + S74.Handshake_hd
  + fixed_sz S621.ProtocolVersion + fixed_sz S7412.Random + fixed_sz S7412.SessionID |.
Definition ciph_len A := nat<=u (A `_ (csuites + sess_len A) `|| A `_ (csuites.+1 + sess_len A)).

(** length of compression methods: smallest possible index and length itself *)
Definition compmeth := (* 46 *) (csuites + '| fixed_sz S7412.CipherSuite |)%nat.
Definition comp_len A := nat<=u (A `_ (compmeth + sess_len A + ciph_len A)).

Definition PolarSSLClientHellop l :=
  l `_ record_flag = S621.handshake /\
  l `_ handshake_flag = S74.client_hello /\
  l `_ maj_ver = S621.SSLv30_maj /\
  l `_ maj_req = S621.SSLv30_maj /\
  S621.length_maxp (n' l) /\
  ('| (S74.Handshake_hd) | + m l <= n l)%nat (* NB: one handshake per record in practice (E. Rescorla, SSL and TLS, Addison-Wesley, 2000 (p.70)) *) /\
  Z<=nat (sess_len l) <= tls_max S7412.SessionID /\
  tls_min S7412.cipher_suites_type <= Z<=nat (ciph_len l) <= tls_max S7412.cipher_suites_type (* NB: in fact, PolarSSL is stricter than the RFC: max is actually 256 *) /\
  ~~ odd (ciph_len l) /\
  tls_min S7412.compression_methods_type <= Z_of_nat (comp_len l) <= tls_max S7412.compression_methods_type (* NB: again, PolarSSL is stricter than the RFC: max is actually 16 *) /\
  (n l + 5 <= size l)%nat /\
  S7412.ClientHello_sz (sess_len l) (ciph_len l) (comp_len l) = Z<=nat (m l) (* NB: extensions are not supported in this version of TLS *).

Definition PolarSSLAssumptions l :=
  l `_ min_ver = S621.TLSv11_min /\
  l `_ min_req = S621.TLSv11_min /\
  l |{ compmeth.+1 + sess_len l + ciph_len l, comp_len l) = nseq (comp_len l) `( 0 )_8.

Definition RecordHandshakeClientHello_decode l :=
  let (a1, l1) := S621.TLSPlainText_header_decode l in
  let '(a2, m, l2) := S74.Handshake_header_decode l1 in
  let (a3, l3) := S7412.ClientHello_decode m l2 in
  (a1 && a2 && a3, l3).

Lemma PolarSSLClientHellop_decode l : PolarSSLClientHellop l ->
  PolarSSLAssumptions l -> (RecordHandshakeClientHello_decode l).1.
Proof.
case=> Hl0 [] Hlclienthello [] Hmajver [] Hmajreq [] Hmaxlen [] Hmn
  [] Hsesslen [] Hciphlen [] Hciphleneven [] HTrue [] nl Hextensions
  [Hminver [Hminreq Hcompression]].
rewrite /RecordHandshakeClientHello_decode /= /S621.TLSPlainText_header_decode.
rewrite  /S74.Handshake_header_decode /S7412.ClientHello_decode.
have Hypo : (compmeth.+1 + sess_len l + ciph_len l + comp_len l <= size l)%nat.
  rewrite /S7412.client_extensions_present /S7412.ClientHello_sz in Hextensions.
  rewrite /= /S7412.Hello_sz ![fixed_sz _]/= in Hextensions.
  eapply leq_trans; last by apply nl.
  apply leq_trans with ('| S74.Handshake_hd | + m l + 5 )%nat; last first.
    by apply leq_add.
  apply leq_trans with (4 + 2 + 32 + 1 + sess_len l + 2 + ciph_len l + 1 + comp_len l + 5)%nat.
    by nat_norm.
  rewrite -!addnA leq_add // !addnA leq_add //.
  apply eq_leq, Z_of_nat_inj.
  rewrite -Hextensions !inj_plus; ring.
have Hypo1 : (rand + 32 <= size l)%nat.
  apply leq_trans with compmeth.+1 => //.
  eapply leq_trans; last by apply Hypo.
  by rewrite -addn1 -2!addnA leq_addr.
have Hypo2 : (sid.+1 + sess_len l <= size l)%nat.
  apply leq_trans with (compmeth.+1 + sess_len l)%nat; first by apply leq_add.
  eapply leq_trans; last by apply Hypo.
  by rewrite -addnA leq_addr.
have Hypo3 : (csuites.+2 + sess_len l + ciph_len l <= size l)%nat.
  apply leq_trans with (compmeth.+1 + sess_len l + ciph_len l)%nat.
    by rewrite /compmeth /= addn2 -2!addnA leq_add.
  eapply leq_trans; last by apply Hypo.
  by rewrite -2!addnA leq_add // -addnA leq_add // leq_addr.
have Hl : l = (S621.handshake :: S621.SSLv30_maj :: l `_ min_ver :: n' l) ++
  (S74.client_hello :: m' l ++ S621.SSLv30_maj :: l `_ min_req :: nil) ++
  (l |{ rand, '| fixed_sz S7412.Random |)) ++
  (l `_ sid :: l |{ sid.+1, sess_len l)) ++
  (l `_ (csuites + sess_len l) :: l `_ (csuites.+1 + sess_len l) ::
   l |{ csuites.+2 + sess_len l, ciph_len l)) ++
  (l `_ (compmeth + sess_len l + ciph_len l) ::
   l |{ compmeth.+1 + sess_len l + ciph_len l , comp_len l)) ++
  drop (compmeth.+1 + sess_len l + ciph_len l + comp_len l) l.
  apply (@eq_from_nth _ zero8).
    do ! rewrite /= !size_cat.
    do ! rewrite size_slice_exact //.
    rewrite size_drop -2!(addnA compmeth.+1) (addnC (compmeth.+1)) !addnS addn0.
    rewrite 3!(addnCA (Pos.to_nat 32)) !addnA.
    set tmp := (sess_len l + _ + _)%nat.
    rewrite [tmp]lock -!addSn -lock (_ : Pos.to_nat 32 = 32%nat) //.
    by rewrite !addnS addn0 addnBA // addnC addnK.
  move=> i Hi.
  clear -Hl0 Hlclienthello Hmajver Hmajreq Hypo Hypo1 Hypo2 Hypo3 Hi.
  do 11 destruct i as [|i] => //.
  rewrite catA nth_cat size_cat ![size _]/= !ltnS ltn0.
  rewrite (_ : i.+3.+4.+4 - (5 + 6) = i)%nat; last by rewrite !addnS addn0 !subnS subn0.
  rewrite nth_cat size_slice_exact // (_ : '| _ | = 32%nat) //.
  case: ifP => H1; first by rewrite nth_slice.
  move/negbT in H1.
  rewrite ltnNge negbK in H1.
  rewrite cat_cons -(cat1s (l `_ sid)) nth_cat [size _]/=.
  rewrite (_ : i - 32 - 1 = i - 33)%nat //; last by rewrite subn1 !subnS.
  rewrite ltnS leq_subLR addn0.
  case: ifP => H2.
    have -> : i = 32%nat.
      apply/eqP; by rewrite eqn_leq H2 H1.
    by rewrite subnn.
  move/negbT in H2.
  rewrite leqNgt negbK in H2.
  rewrite nth_cat size_slice_exact //.
  case: ifP => H3.
    by rewrite nth_slice // addnBA.
  move/negbT in H3.
  rewrite ltnNge negbK in H3.
  rewrite cat_cons -(cat1s (l `_ (csuites + sess_len l))) nth_cat [size _]/=.
  case: ifP => H4.
    have {H3 H4}-> : (sess_len l = i - 33)%nat.
      apply/eqP.
      rewrite eqn_leq H3 /=.
      by rewrite ltnS leq_subLR addn0 in H4.
    by rewrite subnn (_ : i.+3.+4.+4 = csuites + (i - 33))%nat // addnBA.
  move/negbT in H4.
  rewrite -lt0n subn1 /= in H4.
  have {H4}H4 : (sess_len l < i - 33)%nat.
    rewrite ltn_neqAle H3 andbT.
    rewrite lt0n in H4.
    move: H4; apply: contra => /eqP ->.
    by rewrite subnn.
  rewrite (_ : i - 33 - sess_len l - 1 = i - 34 - sess_len l)%nat; last first.
    by rewrite -!subnDA addn1 -addSnnS.
  rewrite cat_cons -(cat1s (l `_ (csuites.+1 + sess_len l))) nth_cat [size _]/=.
  rewrite ltnS leq_subLR addn0.
  have H2' : (33 < i)%nat.
    rewrite -subn_gt0; by apply: leq_ltn_trans H4.
  case: ifP => H5.
    have {H5}H5 : (i = 34 + sess_len l)%nat.
      apply/eqP.
      rewrite ltn_subRL -ltnS -addSn ltnS in H4.
      rewrite eqn_leq H4 andbT.
      by rewrite leq_subLR in H5.
    rewrite {2}H5 (addnC 34%nat) !addnS addn0 !subnS subn0 subnn //.
    by rewrite (_ : _ + _ = i.+3.+4.+4)%nat // (_ : csuites = 44%nat) // H5 -!addSn.
  move/negbT in H5.
  rewrite leqNgt negbK in H5.
  rewrite (_ : i - 34 - sess_len l - 1 = i - 35 - sess_len l)%nat; last first.
    by rewrite -!subnDA addn1 -addSnnS.
  rewrite nth_cat size_slice_exact //.
  have H2'' : (34 < i)%nat.
    rewrite -subn_gt0; by apply: leq_ltn_trans H5.
  case: ifP => H6.
    rewrite nth_slice //.
    congr nth.
    rewrite -!subnDA addnBA; last first.
      rewrite ltn_subRL in H5.
      by rewrite -ltnS addSn ltnS.
    rewrite -!addnA -addnBA; last by rewrite addnC leq_add2l.
    by rewrite (addnC 35%nat) subnDl addnBA.
  move/negbT in H6.
  rewrite -leqNgt in H6.
  rewrite cat_cons -(cat1s (l `_ (compmeth + sess_len l + ciph_len l))) nth_cat [size _]/= ltnS leqn0.
  case: ifP => H7.
    move/eqP : (H7) => ->.
    rewrite (_ : i.+3.+4.+4 = compmeth + sess_len l + ciph_len l)%nat //.
    rewrite subn_eq0 in H7.
    have -> : (ciph_len l = i - 35 - sess_len l)%nat.
      apply/eqP; by rewrite eqn_leq H6 H7.
    rewrite -subnDA addnBA; last first.
      rewrite ltn_subRL in H5.
      by rewrite -ltnS addSn.
    rewrite -addnA -addnBA; last by rewrite addnC leq_add2l.
    rewrite (addnC 35%nat) subnDl /compmeth /csuites ![ '| _ | ]/=.
    by rewrite (_ : Pos.to_nat 44  + Pos.to_nat 2 = 46)%nat // addnBA.
  move/negbT in H7.
  rewrite nth_cat size_slice_exact //.
  have H2''' : (35 < i)%nat.
    rewrite -leqn0 -ltnNge -subnDA ltn_subRL addn0 in H7.
    rewrite -subn_gt0.
    by apply: leq_ltn_trans H7.
  have {H6}H6 : (ciph_len l < i - 35 - sess_len l)%nat.
    rewrite ltn_neqAle H6 andbT.
    move: H7; apply contra => H7.
    move/eqP : H7 => ->.
    by rewrite subnn.
  case: ifP => H8.
    rewrite nth_slice //.
    congr nth.
    rewrite -!subnDA addn1 addnS -addSnnS addnBA; last first.
      rewrite addSn -ltn_subRL.
      by rewrite -leqn0 -ltnNge -subnDA ltn_subRL addn0 in H7.
    rewrite (addnC 36%nat) -2!(addnA) (addnA (sess_len l)) -addnBA; last by rewrite leq_add2l.
    rewrite subnDl /compmeth /csuites ![ '| _ | ]/=.
    by rewrite (_ : Pos.to_nat 44  + Pos.to_nat 2 = 46)%nat // addnBA.
  move/negbT in H8.
  rewrite -leqNgt -!subnDA addn1 addnS -addSnnS in H8.
  rewrite -!subnDA add1n 2!addnS -addSnnS (addnA (sess_len l)) nth_drop.
  congr nth.
  rewrite addnBA; last first.
    rewrite -ltnS -subSn in H8; last first.
      rewrite -subnDA ltn_subRL in H6.
      by rewrite -ltnS addSn.
    rewrite ltn_subRL in H8.
    by rewrite addnA.
  rewrite (addnC 36%nat) -3!addnA (addnA (ciph_len l)) (addnA (sess_len l)) (addnA (sess_len l)).
  rewrite -addnBA; last by rewrite leq_add2l.
  by rewrite subnDl addnBA.
rewrite Hl !cat_cons.
set TAIL := S621.SSLv30_maj :: _.
rewrite (_ : decode _ _ = (true, TAIL)) // {}/TAIL.
set TAIL := l `_ record_sz :: _.
(* we check the protocol version *)
rewrite (_ : decode _ _ = (true, TAIL)) // {}/TAIL cat0s.
set TAIL := S74.client_hello :: _.
rewrite (_ : decode _ _ = (true, TAIL)); last first.
  rewrite /decode /= ifT //.
  apply/leZP.
  rewrite 2!Z_S; omega.
rewrite (_ : S621.proverp _ = true); last first.
  rewrite /= /S621.proverp /= /S621.is_maj /= /S621.is_min /=.
  by rewrite !inE Hminver /= !eqxx !(orbT, orTb).
(* we have parsed the header of the Record packet *)
rewrite Hmaxlen !andTb {}/TAIL.
set TAIL := l `_ handshake_sz :: _.
rewrite (_ : decode _ _ = (true, TAIL)) // {}/TAIL.
set TAIL := S621.SSLv30_maj :: _.
rewrite (_ : decode _ _ = (true, TAIL)); last first.
  rewrite /decode /= ifT //.
  apply/leZP.
  rewrite 3!Z_S; omega.
rewrite (_ : decodep _ _ = true) //= {}/TAIL.
set TAIL := l `_ sid :: _.
rewrite (_ : S621.proverp _ = true); last first.
  rewrite take0 /= /S621.proverp /= /S621.is_maj /= /S621.is_min /=.
  by rewrite !inE Hminreq /= !eqxx !(orbT, orTb).
rewrite (_ : decode _ _ = (true, TAIL)); last first.
  rewrite -{2}(cat0s TAIL).
  apply decode_app.
  rewrite /decode /= ifT; last by rewrite size_slice_exact.
  rewrite ifT; last by rewrite size_drop size_slice_exact.
  by rewrite -take_drop /= -take_drop /= take0.
rewrite {1}/TAIL.
set TAIL2 := l `_ (csuites + sess_len l) :: _.
rewrite (_ : decode _ _ = (true, TAIL2)); last first.
  rewrite -{2}(cat0s TAIL2) -cat_cons.
  apply decode_app.
  by rewrite RFC5246_Prop.decode_SessionID // size_slice_exact.
rewrite {1}/TAIL2.
set TAIL3 := l `_ (compmeth + _ + _) :: _.
rewrite (_ : decode _ _ = (true, TAIL3)); last first.
  rewrite -{2}(cat0s TAIL3) -2!cat_cons.
  apply decode_app, RFC5246_Prop.decode_cipher_suites_type.
    rewrite size_slice_exact // /ciph_len /(nat<=i8) /MachineIntByte_m.bytes2nat.
    by rewrite /bSum_c /= /u2nat u2Z_concat 2!u2ZE.
  by rewrite size_slice_exact.
rewrite {1}/TAIL3.
set TAIL4 := drop _ _.
rewrite (_ : decode _ _ = (true, TAIL4)); last first.
  rewrite Hcompression -{2}(cat0s TAIL4) -cat_cons.
  by apply decode_app, RFC5246_Prop.decode_compression_methods_type.
rewrite ifF // -/(m' l).
apply/negbTE.
set tmp := (_ - _)%nat.
have -> : tmp = sess_len l.
  rewrite /tmp /TAIL /TAIL2 -cat_cons size_cat addnK /sess_len /=.
  by rewrite size_slice_exact // subn1.
rewrite {}/tmp.
set tmp := (_ - _)%nat.
have -> : tmp = ciph_len l.
  by rewrite /tmp /TAIL2 /TAIL3 -2!cat_cons size_cat addnK /ciph_len /= size_slice_exact // subn2.
rewrite {}/tmp /S7412.client_extensions_present -Hextensions ltZNge' negbK.
set tmp := (_ - _)%nat.
suff Htmp : (comp_len l <= tmp)%nat.
  rewrite /S7412.ClientHello_sz [fixed_sz _]/=.
  exact/leZP/leZ_add2l/inj_le/leP.
rewrite /tmp /TAIL3 /= /TAIL4 size_cat size_slice_exact // size_drop subSn; last by rewrite leq_addl.
by rewrite addnK subn1.
Qed.

(** ssl_default_ciphers array in library/ssl_tls.c *)

Program Definition CipherSuite_to_i32 (p : S7412.CipherSuitePacket) : int 32 :=
  zero16 `|| (i16<=i8 p _).
Next Obligation.
by apply RFC5246_Prop.size_CipherSuitePacket.
Defined.

Lemma CipherSuite_to_i32_NULL : CipherSuite_to_i32 A5.TLS_NULL_WITH_NULL_NULL = u32<=Z 0.
Proof.
rewrite /CipherSuite_to_i32 /CipherSuite_to_i32_obligation_1.
apply u2Z_inj.
rewrite (@u2Z_concat 16 16) /zero16 Z2uK // mul0Z add0Z (_ : i16<=i8 _ _ = zero16); last first.
  apply int_flat_int_flat_ok => /=.
  apply int_break_flat => //.
  rewrite int_break_0 //= /MachineIntByte_m.hex2t /=.
  congr cons.
    by apply u2Z_inj; rewrite (@u2Z_concat 4) /= -!Z2uE !Z2uK.
  congr cons.
  by apply u2Z_inj; rewrite (@u2Z_concat 4) /= -!Z2uE !Z2uK.
by rewrite !Z2uK.
Qed.

Definition SSL_EDH_RSA_AES_128_SHA := CipherSuite_to_i32 A5.TLS_DHE_RSA_WITH_AES_128_CBC_SHA.
Definition SSL_EDH_RSA_AES_256_SHA := CipherSuite_to_i32 A5.TLS_DHE_RSA_WITH_AES_256_CBC_SHA.
Definition SSL_EDH_RSA_CAMELLIA_128_SHA := CipherSuite_to_i32 TLS_DHE_RSA_WITH_CAMELLIA_128_CBC_SHA.
Definition SSL_EDH_RSA_CAMELLIA_256_SHA := CipherSuite_to_i32 TLS_DHE_RSA_WITH_CAMELLIA_256_CBC_SHA.
Definition SSL_EDH_RSA_DES_168_SHA := CipherSuite_to_i32 A5.TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA.
Definition SSL_RSA_AES_256_SHA := CipherSuite_to_i32 A5.TLS_RSA_WITH_AES_256_CBC_SHA.
Definition SSL_RSA_CAMELLIA_256_SHA := CipherSuite_to_i32 TLS_RSA_WITH_CAMELLIA_256_CBC_SHA.
Definition SSL_RSA_AES_128_SHA := CipherSuite_to_i32 A5.TLS_RSA_WITH_AES_128_CBC_SHA.
Definition SSL_RSA_CAMELLIA_128_SHA := CipherSuite_to_i32 TLS_RSA_WITH_CAMELLIA_128_CBC_SHA.
Definition SSL_RSA_DES_168_SHA := CipherSuite_to_i32 A5.TLS_RSA_WITH_3DES_EDE_CBC_SHA.
Definition SSL_RSA_RC4_128_SHA := CipherSuite_to_i32 A5.TLS_RSA_WITH_RC4_128_SHA.
Definition SSL_RSA_RC4_128_MD5 := CipherSuite_to_i32 A5.TLS_RSA_WITH_RC4_128_MD5.

Definition largest_ssl_default_ciphers :=
  SSL_EDH_RSA_AES_128_SHA :: SSL_EDH_RSA_AES_256_SHA :: SSL_EDH_RSA_CAMELLIA_128_SHA ::
  SSL_EDH_RSA_CAMELLIA_256_SHA :: SSL_EDH_RSA_DES_168_SHA :: SSL_RSA_AES_256_SHA ::
  SSL_RSA_CAMELLIA_256_SHA :: SSL_RSA_AES_128_SHA :: SSL_RSA_CAMELLIA_128_SHA ::
  SSL_RSA_DES_168_SHA :: SSL_RSA_RC4_128_SHA :: SSL_RSA_RC4_128_MD5 ::
  CipherSuite_to_i32 A5.TLS_NULL_WITH_NULL_NULL :: nil.

Definition no_zero_non_empty l :=
  ((forall i, i < size l -> l `32_ i != zero32) /\ (0 < size l))%nat.

Definition ciphers_seq l :=
  (exists l', no_zero_non_empty l' /\
   l = rcons l' (CipherSuite_to_i32 A5.TLS_NULL_WITH_NULL_NULL)) /\
  (size l <= size largest_ssl_default_ciphers)%nat (* 13 *).

Definition Final_bu SI bu : assert := sepex BU',
  (!!(BU' |{ 8, '| S621.TLSPlainText_hd | + n SI) =
      SI |{ 0, '| S621.TLSPlainText_hd | + n SI))) ** [ bu ]c |---> map phy<=ui8 BU'.

Definition Ssl_context server_status majv minv mmaj mmin
  (ses : (:* (g.-typ: ssl_session)).-phy) (bu : (:* (g.-ityp: uchar)).-phy)
  inleft md5s sha1s (ciphers : (:* (g.-ityp: sint)).-phy)
  (rb : (:* (g.-ityp: uchar)).-phy)  : assert :=
  __ssl |le~> mk_ssl_context server_status
    majv minv mmaj mmin (ptr<=phy ses)
    (ptr<=phy bu `+ `( 8 )_ptr_len) (ptr<=phy bu `+ `( 13 )_ ptr_len)
    inleft md5s sha1s (ptr<=phy ciphers) (ptr<=phy rb).

Definition Final_ses SI CI (ses : (:* (g.-typ: ssl_session)).-phy)
  (id : (:* (g.-ityp: uchar)).-phy) := sepex i, sepex k, sepex chosen_cipher,
  (let j := 2 * k in
  !!(chosen_cipher = zext 16 (SI `_ (compmeth + sess_len SI + j))
                 `|| (SI `_ (compmeth + sess_len SI + j + 1))) **
  !!(chosen_cipher = CI `32_ i) **
  (ses |lV~> mk_ssl_session
    chosen_cipher `(Z<=nat (sess_len SI))_32 (ptr<=phy id)))%nat.

Definition Final_rb SI RB rb := [ rb ]c |---> map phy<=ui8
  (SI |{ rand, '| (tls_max S7412.Random) |) ++ drop ('| (tls_max S7412.Random) |) RB).

Definition Final_id SI id := [ id ]c |--->
  map phy<=ui8 (SI |{ sid.+1, sess_len SI)) ++ nseq (32 - sess_len SI) pv0.

Definition error := `! \~b \b __ret \= [ 0 ]sc ** TT.

Definition success := `! \b __ret \= [ 0 ]sc.

Lemma POLAR_ret_err P Q err_msg : - 2 ^^ 31 < err_msg < 0 ->
  {{ P }} _ret <- [ err_msg ]sc; Return {{ error \\// Q }}.
Proof.
move=> Herr_msg.
apply hoare_seq with error.
+ apply hoare_assign_stren.
  rewrite /error.
  Ent_R_subst_con_distr.
  do 2 Ent_R_subst_apply.
  Bbang2sbang.
  apply ent_R_sbang_con; last by [].
  Rewrite_ground_bexp @sequiv_bop_re_sc => //=.
    simpl expZ in Herr_msg; omega.
  rewrite (_ : err_msg == 0 = false); last by apply/negbTE/eqP; omega.
  by apply: bneg_0uc.
+ by apply skip_hoare, ent_R_or_1.
Qed.

Lemma is_not_last_of_zero_terminated {A : eqType} (s : seq A) (zero : A) i :
  last zero s = zero -> (i < size s)%nat -> nth zero s i != zero -> (i.+1 < size s)%nat.
Proof.
move=> Hzero i_s i_zero.
apply/negPn/negP => abs.
rewrite -ltnNge ltnS in abs.
have {abs i_s} abs : size s = i.+1.
  rewrite leq_eqVlt in abs.
  case/orP : abs => [/eqP // | abs].
  exfalso.
  rewrite ltnS in abs.
  move: (leq_ltn_trans abs i_s); by rewrite ltnn.
rewrite (@last_nth _ zero) abs /= in Hzero.
by rewrite Hzero eqxx in i_zero.
Qed.

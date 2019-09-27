(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Div2 Even.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple.
Require Import ZArith_ext String_ext.
Require Import ssrnat_ext ssrZ seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_expr_equiv C_expr_ground.
Require Import C_seplog C_tactics.
Require Import rfc5246.
Import RFC5932.
Require Import POLAR_library_functions POLAR_library_functions_triple.
Require Import POLAR_ssl_ctxt POLAR_parse_client_hello POLAR_parse_client_hello_header.
Require Import POLAR_parse_client_hello_triple2.

Local Close Scope select_scope.

Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope seq_ext_scope.
Local Open Scope C_types_scope.
Local Open Scope C_value_scope.
Local Open Scope C_expr_scope.
Local Open Scope C_assert_scope.
Local Open Scope C_cmd_scope.

(** * Verification of the ClientHello Parsing Program (1/4) *)

Section POLAR_parse_client_hello_triple.

(** socket input *)
Variable SI : seq (int 8).

Lemma POLAR_parse_client_hello_triple1 (BU RB ID : seq (int 8)) (CI : seq (int 32))
  (sz_BU : size BU = '| SSL_BUFFER_LEN |)
  (sz_RB : size RB = 64) (sz_ID : size ID = 32)
  (HCI : ciphers_seq CI)
  (majv0 minv0 mmaj0 mmin0 cipher0 length0 : int 32)
  (bu rb id : (:* (ityp: uchar)).-phy)
  (ses : (:* (g.-typ: ssl_session)).-phy)
  (ciphers : (:* (ityp: sint)).-phy)
  (vssl : int ptr_len)
  (md5s sha1s : 5.-tuple (int ptr_len)) :
  let init_ssl_var := `! \b __ssl \= [ phy<=ptr _ vssl ]c in
  let init_bu := [ bu ]c |---> map phy<=ui8 BU in
  let init_rb := [ rb ]c |---> map phy<=ui8 RB in
  let init_id := [ id ]c |---> map phy<=ui8 ID in
  let init_ses := ses |lV~> mk_ssl_session cipher0 length0 (ptr<=phy id) in
  let init_ciphers := [ ciphers ]c |--> map phy<=si32 CI in
  let init_ssl_context := Ssl_context (zext 24 S74.client_hello) majv0 minv0
    mmaj0 mmin0 ses bu `( 0 )_32 md5s sha1s ciphers rb in
  let final_bu := Final_bu SI bu in
  let final_ses := Final_ses SI CI ses id in
  let final_rb := Final_rb SI RB rb in
  let final_id := Final_id SI id  in
  let final_ssl_context := Ssl_context (zext 24 S74.server_hello)
    (zext 24 (SI `_ maj_ver))
    (zext 24 (if (u2Z (SI `_ min_req) <=? u2Z (S621.TLSv11_min))%Z then
              SI `_ min_req else S621.TLSv11_min))
    (zext 24 (SI `_ maj_req)) (zext 24 (SI `_ min_req ))
    ses bu `( 0 )s_32 md5s sha1s ciphers rb in
  {{ init_ssl_var ** init_bu ** init_rb ** init_id ** init_ses **
     init_ciphers ** init_ssl_context }}
  ssl_parse_client_hello
  {{ error \\// (success ** final_bu ** final_ses ** final_rb ** final_id **
     final_ssl_context ** !!(PolarSSLClientHellop SI) ** init_ciphers) }}.
Proof.
move=> init_ssl_var init_bu init_rb init_id init_ses init_ciphers
 init_ssl_context final_bu final_ses final_rb final_id final_ssl_context.

unfold ssl_parse_client_hello, ssl_parse_client_hello1.

(** ssl_fetch_input Logic.eq_refl _ret Logic.eq_refl __ssl [ 5 ]sc; *)

idtac "1) ssl_fetch_input".

pose Hbu := sepex BU1, [ bu ]c |---> map phy<=ui8 BU1 **
  !!(BU1 |{ 8 + '| (u2Z zero32) |, 5) = SI |{ '| (u2Z zero32) |, 5)) **
  !!(BU1 |{ 8, '| (u2Z zero32) |) = BU |{ 8, '| (u2Z zero32) |)) **
  !!(size BU1 = size BU).
pose size_SI := !!( 4 < size SI ).
pose Hin_left := sepex in_left, Ssl_context (zext 24 S74.client_hello) majv0
  minv0 mmaj0 mmin0 ses bu in_left md5s sha1s ciphers rb **
  !!(in_left = `( 0 )_ 32 `+ `( Z_of_nat 5)_32 ).

apply hoare_seq with (
  init_ssl_var ** init_rb ** init_id ** init_ses ** init_ciphers **
  ((success ** size_SI ** Hin_left ** Hbu) \\// error)).
  Hoare_frame_remove (init_ssl_var :: init_rb :: init_id :: init_ses :: init_ciphers :: nil).
    by rewrite ssl_fetch_input_inde.
  eapply hoare_conseq; last by apply (ssl_fetch_input_triple
    5 `( 0 )_ 32 SI BU majv0 minv0 mmaj0 mmin0 bu rb ses ciphers md5s sha1s).
  - apply ent_L_or; split; [apply ent_R_or_1 | by apply ent_R_or_2].
    rewrite -/success; apply monotony_L.
    rewrite -/size_SI; apply monotony_L.
    rewrite -(add0i `( Z<=nat 5)_ 32) -/Hin_left; apply monotony_L.
    by rewrite [in X in 5 - X]Z2uK.
  - Ent_monotony0.
    by rewrite beq_exx bbang1 coneP sbang_emp.

(** If \b __ret \!= [ 0 ]sc Then *)

idtac "2) ifte".

Hoare_ifte_bang Hret.

(** Return *)
  apply skip_hoare.
  Ent_L_or 0.
  - rewrite [in X in X ===> _]/success /Hret bneq_neg_eq.
    by Ent_L_contradict_idx (0 :: 9 :: nil).
  - Ent_R_or_1.
    rewrite /error; by Ent_decompose (0 :: nil) (0 :: nil).

Hoare_L_or 0; last first.
  rewrite /error -bneq_neg_eq.
  by Hoare_L_contradict (0 :: 7 (* Hret *) :: nil).

Hoare_L_contract_bbang Hret.

unfold Hbu; clear Hbu.
Hoare_L_ex 0 BU1.
set Hbu := [ bu ]c |---> map phy<=ui8 BU1.
Hoare_L_sbang 0 => BU1SI.
rewrite Z2uK //= addn0 in BU1SI.
Hoare_L_sbang 0 => _.
Hoare_L_sbang 0 => sz_BU1.
unfold size_SI; clear size_SI.
Hoare_L_sbang 0 => size_SI.
unfold Hin_left; clear Hin_left.
Hoare_L_ex 0 in_left.
set Hssl_in_left := Ssl_context _ _ _ _ _ _ _ _ _ _ _ _.
Hoare_L_sbang 0 => in_left_5.
rewrite add0i in in_left_5.
clear -sz_BU sz_RB sz_ID BU1SI sz_BU1 size_SI in_left_5 HCI.

(** _buf <-* __ssl &-> get_in_hdr; *)

idtac "3) lookup".

pose Hbuf := `! \b __buf \= [ bu ]c \+ [ 8 ]sc.
Hoare_seq_ext Hbuf.
  Hoare_frame (Hssl_in_left :: nil) (Hssl_in_left :: Hbuf :: nil).
  apply hoare_lookup_fldp_stren, ent_R_lookup_fldp with (pv := phy<=ptr (g.-typ: ityp uchar) (ptr<=phy bu `+ `( 8 )_ ptr_len)).
  - by rewrite get_in_hdr_ssl_ctxt /phylog_conv /=.
  - Ent_R_subst_con_distr.
    rewrite /Hssl_in_left /Ssl_context.
    do 2 Ent_R_subst_apply.
    Ent_monotony0.
    by rewrite sequiv_add_p_cst.

(** _buf0 <-* __buf; *)

idtac "4) lookup".

pose Hbuf0 := `! \b __buf0 \= [ BU1 `_ 8  ]pc.
Hoare_seq_ext Hbuf0.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf0 :: nil).
  apply hoare_lookup_mapstos_fit_stren with (l := map phy<=ui8 BU1) (e := [ bu ]c) (i := 8).
    by rewrite size_map sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  apply ent_R_lookup_mapstos_fit_trans.
  - by rewrite size_map sz_BU1 sz_BU.
  - Ent_R_conA'.
    rewrite conC; by apply ent_R_con_T.
  - Ent_R_subst_con_distr.
    rewrite [nth] lock.
    do 3 Ent_R_subst_apply.
    apply monotony_L.
    rewrite -/Hbuf -lock (nth_map zero8); last by rewrite sz_BU1 sz_BU.
    by Ent_monotony0.

(** If \b (__buf0 \& [ 128 ]uc) \!= [ 0 ]uc Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "5) ifte".
Hoare_ifte_bang Hbuf0_128; first by apply POLAR_ret_err.

(** If \b __buf0 \!= [ SSL_MSG_HANDSHAKE ]c  Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "6) ifte".
Hoare_ifte_bang Hbuf0_handshake; first by apply POLAR_ret_err.

(** _buf1 <-* __buf \+ [ 1 ]sc; *)

idtac "7) lookup".

pose Hbuf1 := `! \b __buf1 \= ([ BU1 `_ 9 ]pc : exp sigma (ityp: uchar)).
Hoare_seq_ext Hbuf1.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf1 :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 9) (l := map phy<=ui8 BU1) (e := [ bu ]c).
    by rewrite size_map sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  apply ent_R_lookup_mapstos_fit_trans.
  - by rewrite size_map sz_BU1 sz_BU.
  - Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
    Ent_decompose (0 :: nil) (0 :: nil); last by done.
    unfold Hbuf.
    Ent_R_rewrite_eq_p 0.
    Ent_R_subst_apply.
    rewrite CaddnpA // sequiv_add_e_sc_pos //; by Ent_monotony0.
  - rewrite [nth] lock.
    Ent_R_subst_con_distr.
    do 3 Ent_R_subst_apply.
    apply monotony_L.
    rewrite -lock (nth_map zero8); last by rewrite sz_BU1 sz_BU.
    by Ent_monotony0.

(** If \b __buf1 \!= [ SSL_MAJOR_VERSION_3 ]c Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "8) ifte".

Hoare_ifte_bang Hbuf1_majversion; first by apply POLAR_ret_err.

(** _buf3 <-* __buf \+ [ 3 ]sc; *)

idtac "9) lookup".

pose BU19 := !!( BU1 `_ 9 = S621.SSLv30_maj).

Hoare_L_stren_by BU19 (Hbuf1 :: Hbuf1_majversion :: nil).
  unfold Hbuf1, Hbuf1_majversion, BU19.
  Ent_LR_rewrite_eq_e 0 (* buf1 *).
  Ent_R_subst_apply; Ent_L_subst_apply.
  rewrite bneq_neg_eq bnegK.
  Bbang2sbang.
  apply ent_sbang_sbang.
  rewrite gb_eq_e 2!ge_cst_e; by case/eqP.

Hoare_L_contract_bbang Hbuf1; Hoare_L_contract_bbang Hbuf1_majversion.
clear Hbuf1 Hbuf1_majversion.
apply hoare_pullout_sbang => {}BU19.

pose Hbuf3 := `! \b __buf3 \= [ BU1 `_ 11 ]pc.
Hoare_seq_ext Hbuf3.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf3 :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 11) (l := map phy<=ui8 BU1) (e := [ bu ]c).
    by rewrite size_map sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  apply ent_R_lookup_mapstos_fit_trans.
  - by rewrite size_map sz_BU1 sz_BU.
  - Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
    Ent_decompose (0 :: nil) (0 :: nil); last by done.
    unfold Hbuf.
    Ent_R_rewrite_eq_p 0.
    Ent_R_subst_apply.
    rewrite CaddnpA // sequiv_add_e_sc //; by Ent_monotony0.
  - rewrite [nth] lock.
    Ent_R_subst_con_distr.
    do 3 Ent_R_subst_apply.
    apply monotony_L.
    rewrite -lock (nth_map zero8); last by rewrite sz_BU1 sz_BU.
    by Ent_monotony0.

(** _buf4 <-* __buf \+ [ 4 ]sc; *)

idtac "10) lookup".

pose Hbuf4 := `! \b __buf4 \= [ BU1 `_ 12 ]pc.
Hoare_seq_ext Hbuf4.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf4 :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 12) (l := map phy<=ui8 BU1) (e := [ bu ]c).
  - by rewrite size_map sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  - apply ent_R_lookup_mapstos_fit_trans.
    - by rewrite size_map sz_BU1 sz_BU.
    - Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
      Ent_decompose (0 :: nil) (0 :: nil); last by done.
      unfold Hbuf.
      Ent_R_rewrite_eq_p 0.
      Ent_R_subst_apply.
      rewrite CaddnpA // sequiv_add_e_sc //; by Ent_monotony0.
    - Ent_R_subst_con_distr.
      rewrite [nth] lock.
      do 3 Ent_R_subst_apply.
      apply monotony_L.
      rewrite -lock (nth_map zero8); last by rewrite sz_BU1 sz_BU.
      by Ent_monotony0.

(** _n <- (int) __buf3 \<< [ 8 ]sc \| (int) __buf4; *)

idtac "11) assign".

pose Hn := `! \b __n \= ( (int) ([ BU1 `_ 11 ]pc : exp _ (ityp: uchar)) \<< [8 ]sc \| 
  (int) ([ BU1 `_ 12 ]pc : exp _ (ityp: uchar))).
Hoare_seq_ext Hn.
  rewrite {1}(bbang_dup2 Hbuf3 Logic.eq_refl).
  rewrite {1}(bbang_dup2 Hbuf4 Logic.eq_refl).
  Hoare_frame (Hbuf3 :: Hbuf4 :: nil) (Hn :: nil).
  apply hoare_assign_stren.
  Ent_R_subst_apply.
  unfold Hbuf3.
  Ent_R_rewrite_eq_e 0 (* buf3 *).
  Ent_R_subst_apply.
  unfold Hbuf4.
  Ent_LR_rewrite_eq_e 0 (* buf4 *).
  Ent_R_subst_apply.
  by Ent_monotony0.

(** If \b __n \< [ 45 ]sc Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "12) ifte".
Hoare_ifte_bang Hn_45; first by apply POLAR_ret_err.

(** If \b __n \> [ 512 ]sc Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "13) ifte".

Hoare_ifte_bang Hn_512; first by apply POLAR_ret_err.

unfold ssl_parse_client_hello2.

(** ssl_fetch_input erefl _ret erefl __ssl ([ 5 ]sc \+ __n); *)

idtac "14) ssl_fetch_input".

pose the_n := s2Z ((zext 24 (BU1 `_ 11)) `<< 8 `|` zext 24 (BU1 `_ 12)).
pose the_n_plus5 := (5 + the_n)%Z.

pose Hbu_new := sepex BU2, [ bu ]c |---> map phy<=ui8 BU2 **
    (!!(BU2 |{ 8 + 5, '| the_n |) = SI |{ 5, '| the_n |))) **
    !!(BU2 |{ 8, 5) = BU1 |{ 8, 5)) ** !!(size BU2 = size BU1).
pose min_SI := !!( '| the_n_plus5 | <= size SI ).
pose Hin_left_success := sepex in_left0, Ssl_context
    (zext 24 S74.client_hello) majv0 minv0 mmaj0 mmin0
    ses bu in_left0 md5s sha1s ciphers rb **
    !!(in_left0 = Z2u 32 the_n_plus5).

apply hoare_stren_pull_out with (a := (45 <= the_n /\ the_n <= 512)%Z).
  Ent_decompose (0 (* Hn *) :: 15 (* Hn_45 *):: 16 (* Hn_512 *) :: nil) (0 :: nil); last by done.
  unfold Hn, Hn_45, Hn_512.
  Ent_LR_rewrite_eq_e 0 (* n *).
  (do 2 Ent_L_subst_apply); Ent_R_subst_apply.
  Bbang2sbang.
  Ent_L_sbang 0 => H.
  rewrite -(ground_bexp_sem (store0 sigma)) in H.
  rewrite <- CgeqNlt in H.
  apply bop_re_ge_Zge in H.
  apply Z.ge_le in H.
  rewrite 2!(ground_exp_sem (store0 sigma)) s2Z_ge_s_cst_e in H; last by done.
  have {}H : (45 <= the_n)%Z.
    apply: (leZ_trans H).
    apply Zeq_le.
    rewrite /the_n si32_of_phy_gb_or_e sint_shl_e_to_i32_ge ge_cast_sint_cst_8c phy_of_si32K concat_shl.
    congr (Z<=s (_ `|` _)).
    apply u2Z_inj; rewrite u2Z_castC.
    congr (Z<=u (_ `<< 8)).
    by apply u2Z_inj; rewrite -(@zext_zext _ _ 16 8) (@u2Z_castA 8 16 8).
  Ent_L_sbang 0 => H0.
  rewrite -(ground_bexp_sem (store0 sigma)) in H0.
  rewrite <- CleqNgt in H0.
  apply bop_re_le_Zle in H0.
  rewrite 2!(ground_exp_sem (store0 sigma)) in H0.
  rewrite s2Z_ge_s_cst_e in H0; last by done.
  have {}H0 : (the_n <= 512)%Z.
    apply: (leZ_trans _ H0).
    apply Zeq_le.
    rewrite /the_n si32_of_phy_gb_or_e sint_shl_e_to_i32_ge ge_cast_sint_cst_8c phy_of_si32K concat_shl.
    congr (Z<=s (_ `|` _)).
    apply u2Z_inj; rewrite u2Z_castC.
    congr (Z<=u (_ `<< _)).
    apply u2Z_inj; by rewrite -(@zext_zext _ _ 16 8) (@u2Z_castA 8 16 8).
  by apply ent_R_sbang.

case=> HN1 HN2.

apply hoare_seq with (
  init_ssl_var ** init_rb ** init_id ** init_ses ** init_ciphers **
  Hbuf ** Hbuf0 ** Hbuf0_128 ** Hbuf0_handshake ** Hbuf3 ** Hbuf4 ** Hn ** Hn_45 ** Hn_512 **
  ((success ** min_SI ** Hin_left_success ** Hbu_new) \\// error)).
  set C := ssl_fetch_input _ _ _ _ _.
  Hoare_L_contract_bbang success.
  pose Hnexp := `! \b [5 ]sc \+ __n \= [ Z<=nat ('| the_n_plus5 |) ]sc.
  pose Hpre := !!(Z<=nat ('| the_n_plus5 |) < POLAR_library_functions_triple.SSL_BUFFER_LEN)%Z.
  Hoare_L_stren_by (Hnexp ** Hpre) (Hn :: nil).
    rewrite /Hnexp /Hpre /Hn /Hn_45 /Hn_512 Z_of_nat_Zabs_nat; last by unfold the_n_plus5; omega.
    Ent_R_rewrite_eq_e 0 (* n *).
    Ent_R_subst_con_distr.
    do 2 Ent_R_subst_apply.
    Bbang2sbang.
    Ent_R_sbang 0.
      unfold the_n_plus5.
      set the_n' := _ \| _.
      have : the_n' =s ([ the_n ]sc (*: exp sigma _*) ).
        move=> s.
        Transparent eval. rewrite /the_n' /the_n /=. Opaque eval.
        rewrite !i8_of_i32K (_ : '| Z<=u `( 8 )s_32 | = 8); last first.
          by rewrite -s2Z_u2Z_pos !Z2sK.
        apply mkPhy_irrelevance => //=; by rewrite Z2s_s2Z.
      move=> X.
      Rewrite_ground_bexp X.
      Rewrite_ground_bexp @sequiv_add_e_sc_pos; last 4 first.
        by vm_compute.
        by apply: leZ_trans HN1.
        simpl expZ; omega.
        Rewrite_ground_bexp @beq_exx.
        by apply: oneuc.
    Ent_R_sbang 0; last by done.
    rewrite /the_n_plus5 /POLAR_library_functions_triple.SSL_BUFFER_LEN; omega.

  Hoare_frame_remove (Hn :: Hbuf4 :: Hbuf3 :: Hbuf0 :: Hbuf :: init_ssl_var :: init_rb :: init_id :: init_ses :: init_ciphers :: Hbuf0_128 :: Hbuf0_handshake :: Hn_45 :: Hn_512 :: nil); first by rewrite ssl_fetch_input_inde.
  eapply hoare_conseq; last by apply (ssl_fetch_input_triple ('| the_n_plus5 |)
    in_left SI BU1 majv0 minv0 mmaj0 mmin0 bu rb ses ciphers md5s sha1s).
  - rewrite -/success -/min_SI -/error Z_of_nat_Zabs_nat; last by rewrite /the_n_plus5; omega.
    rewrite -/Hin_left_success (_: '| the_n_plus5 | - '| (u2Z in_left) | = '| the_n |); last first.
      rewrite in_left_5 Z2uK // Zabs_nat_Z_of_nat // /the_n_plus5 Zabs_nat_Zplus //; last by omega.
      by rewrite (_ : '| 5 | = 5) // plusE addnC -addnBA ?addn0.
    by rewrite -/Hbu_new in_left_5 Z2uK.
  - rewrite -/Hssl_in_left -/Hbu -/Hpre -/Hnexp; by Ent_permut.

(** If \b __ret \!= [ 0 ]sc Then *)

idtac "15) ifte".

Hoare_ifte_bang Hret.

(** ret *)
  apply skip_hoare.
  Ent_L_or 0.
  - let l := Ent_L_Find_indices (success :: Hret :: nil) in
    unfold Hret; rewrite bneq_neg_eq;
    by Ent_L_contradict_idx l.
  - Ent_R_or_1.
    rewrite /error; by Ent_decompose (0 :: nil) (0 :: nil).

set C := _; _.

Hoare_L_or 0; last first.
  unfold error; rewrite <- bneq_neg_eq; unfold Hret.
  by Hoare_L_contradict (0 :: 16 :: nil).

Hoare_L_contract_bbang Hret.

unfold Hin_left_success; Hoare_L_ex 0 in_left2.

clear Hssl_in_left; set Hssl_in_left2 := Ssl_context (zext 24 S74.client_hello)
  majv0 minv0 mmaj0 mmin0 ses bu in_left2 md5s sha1s ciphers rb.

Hoare_L_sbang 0 => Hin_left2.

unfold Hbu_new; Hoare_L_ex 0 BU2.
clear Hbu; set Hbu := [ bu ]c |---> map phy<=ui8 BU2.
Hoare_L_sbang 0 => BU2SI.
Hoare_L_sbang 0 => BU2BU1.
Hoare_L_sbang 0 => sz_BU2.
rewrite /min_SI {min_SI}.
Hoare_L_sbang 0 => min_SI.

idtac "16) lookup".

Hoare_L_contract_bbang Hbuf; clear Hbuf.
unfold C; clear C.

(** _buf <-* __ssl &-> _in_msg; *)

pose Hbuf := `! \b __buf \= [ bu ]c \+ [ 13 ]sc.
Hoare_seq_ext Hbuf.
  Hoare_frame (Hssl_in_left2 :: nil) (Hssl_in_left2 :: Hbuf :: nil).
  apply hoare_lookup_fldp_stren, ent_R_lookup_fldp with (pv := phy<=ptr (g.-typ: ityp uchar) (ptr<=phy bu `+ `( 13 )_ ptr_len)).
  - by rewrite get_in_msg_ssl_ctxt /phylog_conv /=.
  - Ent_R_subst_con_distr.
    unfold Hssl_in_left2, Ssl_context.
    do 2 Ent_R_subst_apply.
    by rewrite -/(Ssl_context _ _ _ _ _ _ _ _ _ _ _ _) sequiv_add_p_cst // beq_pxx bbang1 conPe.

(** _n0 <-* __ssl &-> _in_left; *)

idtac "17) lookup".

pose Hn0 := `! \b __n0 \= [ phy<=si32 in_left2 ]c.
Hoare_seq_ext Hn0.
  Hoare_frame (Hssl_in_left2 :: nil) (Hssl_in_left2 :: Hn0 :: nil).
  apply hoare_lookup_fldp_stren, ent_R_lookup_fldp with (pv := phy<=si32 in_left2).
  - by rewrite get_in_left_ssl_ctxt /phylog_conv /=.
  - Ent_R_subst_con_distr.
    unfold Hssl_in_left2, Ssl_context.
    do 2 Ent_R_subst_apply.
    by Ent_monotony0.

Hoare_L_contract_bbang Hn_45; Hoare_L_contract_bbang Hn_512.

(** _n_old <- __n; *)

idtac "17bis) assign".

pose Hn_old := `! \b __n_old \= [ the_n ]sc.
Hoare_seq_ext Hn_old.
  rewrite {1}(bbang_dup2 Hn Logic.eq_refl).
  Hoare_frame (Hn :: nil) (Hn_old :: nil).
  apply hoare_assign_stren.
  unfold Hn, Hn_old.
  Ent_R_subst_apply.
  Ent_LR_rewrite_eq_e 0 (* n *).
  Ent_R_subst_apply.
  unfold the_n.
  Bbang2sbang.
  apply ent_R_sbang.
  rewrite gb_eq_e ge_cst_e.
  apply/eqP/si32_of_phy_inj.
  rewrite si32_of_phy_gb_or_e ge_cast_sint_cst_8c [in X in _ `|` X = _] phy_of_si32K.
  rewrite sint_shl_e_to_i32_ge phy_of_si32K Z2s_s2Z.
  congr (_ `|` _).
  rewrite concat_shl.
  apply u2Z_inj; rewrite u2Z_castC.
  congr (Z<=u (_ `<< _)).
  apply u2Z_inj.
  by rewrite !u2Z_zext (u2Z_zext 24).

Hoare_L_contract_bbang Hn.

(** _n <- __n0 \- [ 5 ]sc; *)

idtac "18) assign".

clear Hn; set Hn := `! \b __n \= __n0 \- [ 5 ]sc.
Hoare_seq_ext Hn.
  Hoare_frame (@Nil assert) (Hn :: nil).
  apply hoare_assign_stren.
  Ent_R_subst_apply.
  by Ent_monotony0.

(** md5_update Logic.eq_refl (__ssl .=> get_fin_md5) __buf __n; *)

idtac "19) md51_update".

match goal with
  | |- {{ ?P }} _ {{ _ }} => apply hoare_seq with P
end.

admit.

(** sha1_update Logic.eq_refl (__ssl .=> get_fin_sha1) __buf __n; *)

idtac "20) sha1_update".

match goal with
  | |- {{ ?P }} _ {{ _ }} => apply hoare_seq with P
end.

admit.

(** _buf0 <-* __buf; *)

idtac "21) lookup".

pose BU18 := !!( BU1 `_ 8 `& Z2u 8 128  = Z2u 8 0 /\ BU1 `_ 8 = S621.handshake (*SSL_MSG_HANDSHAKE*) ).

Hoare_L_stren_by BU18 (Hbuf0 :: Hbuf0_128 :: Hbuf0_handshake :: nil).
  rewrite /Hbuf0 /Hbuf0_128 /Hbuf0_handshake /BU18.
  Ent_LR_rewrite_eq_e 0 (* buf0 *).
  Ent_R_subst_apply; do 2 Ent_L_subst_apply.
  rewrite bneq_neg_eq bneq_neg_eq bnegK bnegK bbang_and.
  set btmp := \b _.
  rewrite (@ground_bbang_sbang btmp Logic.eq_refl).
  apply ent_sbang_sbang.
  rewrite and_gb.
  case/andP.
  rewrite 2!gb_eq_e and_8c 2!ge_cst_e.
  case/eqP => ->.
  rewrite 2!ge_cst_e.
  case/eqP => ->.
  by rewrite /S621.handshake -Z2uE.

Hoare_L_contract_bbang Hbuf0 ;
Hoare_L_contract_bbang Hbuf0_128 ;
Hoare_L_contract_bbang Hbuf0_handshake.
clear Hbuf0 Hbuf0_128 Hbuf0_handshake.
apply hoare_pullout_sbang => {}BU18.

pose Hbuf0 := `! \b __buf0 \= ([  BU2 `_ 13 ]pc : exp sigma (ityp: uchar)).
Hoare_seq_ext Hbuf0.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf0 :: nil).
  eapply hoare_lookup_mapstos_fit_stren with (i := 13) (l := map phy<=ui8 BU2).
  - by rewrite size_map sz_BU2 sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  - apply ent_R_lookup_mapstos_fit_trans.
    + by rewrite size_map sz_BU2 sz_BU1 sz_BU.
    + rewrite /Hbu /Hbuf conC.
      Ent_R_conA'.
      by apply ent_R_con_T.
    + rewrite /Hbuf [nth] lock.
      Ent_R_subst_con_distr.
      do 3 Ent_R_subst_apply.
      apply monotony_L.
      rewrite -lock (nth_map zero8); last by rewrite sz_BU2 sz_BU1 sz_BU.
      by Ent_monotony0.

(** If \b __buf0 \!= [ SSL_HS_CLIENT_HELLO ]c Then *)
(** _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "22) ifte".

Hoare_ifte_bang Hbuf0_clienthello; first by apply POLAR_ret_err.

pose BU2_13 := !!( BU2 `_ 13 = S74.client_hello ).

Hoare_L_stren_by BU2_13 (Hbuf0 :: Hbuf0_clienthello :: nil).
  rewrite /Hbuf0 /Hbuf0_clienthello /BU2_13.
  Ent_LR_rewrite_eq_e 0 (* buf0 *).
  do 2 Ent_LR_subst_apply.
  rewrite bneq_neg_eq bnegK.
  set btmp := \b _.
  rewrite (@ground_bbang_sbang btmp Logic.eq_refl).
  apply ent_sbang_sbang.
  rewrite gb_eq_e 2!ge_cst_e; case/eqP => ->.
  by rewrite /S74.client_hello -Z2uE.

apply hoare_pullout_sbang => {}BU2_13.

Hoare_L_contract_bbang Hbuf0; Hoare_L_contract_bbang Hbuf0_clienthello.
clear Hbuf0 Hbuf0_clienthello.

(** _buf4 <-* __buf \+ [ 4 ]sc; *)

idtac "23) lookup".

Hoare_L_contract_bbang Hbuf4; clear Hbuf4.

pose Hbuf4 := `! \b __buf4 \= ([ BU2 `_ 17 ]pc : exp sigma (ityp: uchar)).
Hoare_seq_ext Hbuf4.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf4 :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 17) (l := map phy<=ui8 BU2) (e := [ bu ]c).
  - by rewrite size_map sz_BU2 sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  - apply ent_R_lookup_mapstos_fit_trans.
    + by rewrite size_map sz_BU2 sz_BU1 sz_BU.
    + Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
      Ent_decompose (0 :: nil) (0 :: nil); last by done.
      unfold Hbuf.
      Ent_LR_rewrite_eq_p 0 (* buf *).
      Ent_R_subst_apply.
      rewrite CaddnpA // sequiv_add_e_sc_pos //; by Ent_monotony0.
    - rewrite /Hbuf [nth] lock.
      Ent_R_subst_con_distr.
      do 3 Ent_LR_subst_apply.
      apply monotony_L.
      rewrite -lock (nth_map zero8); last by rewrite sz_BU2 sz_BU1 sz_BU.
      by Ent_monotony0.

(** If \b __buf4 \!= [ SSL_MAJOR_VERSION_3 ]c Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "24) ifte".

Hoare_ifte_bang Hbuf4_majversion; first by apply POLAR_ret_err.

(** __ssl &-> _major_ver *<- (int) ([ SSL_MAJOR_VERSION_3 ]c); *)

idtac "25) mutation".

(* NB: reuse safe case rather than zext directly *)
pose Hssl_majver := Ssl_context (zext 24 S74.client_hello)
  (si32<=phy (safe_cast_phy SSL_MAJOR_VERSION_3 sint erefl))
  minv0 mmaj0 mmin0 ses bu in_left2 md5s sha1s ciphers rb.

Hoare_seq_replace1 Hssl_in_left2 Hssl_majver.
  Hoare_frame (Hssl_in_left2 :: nil) (Hssl_majver :: nil).
  eapply hoare_weak; last by apply hoare_mutation_fldp_local_forward.
  move => s h.
  move/(_ (mkSintLog (si32<=phy ([ (int) ([ SSL_MAJOR_VERSION_3 ]c) ]_s)))).
  rewrite /phylog_conv [in X in ((X -> _ ) -> _)]/= si32_of_phyK eqxx.
  move/(_ erefl).
  by rewrite set_major_ver_ssl_ctxt.

(** _buf5 <-* __buf \+ [ 5 ]sc; *)

idtac "26) lookup".
pose Hbuf5 := `! \b __buf5 \= ([ BU2 `_ 18 ]pc : exp sigma (ityp: uchar)).
Hoare_seq_ext Hbuf5.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf5 :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 18) (l := map phy<=ui8 BU2) (e := [ bu ]c).
  - by rewrite size_map sz_BU2 sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  - apply ent_R_lookup_mapstos_fit_trans.
    + by rewrite size_map sz_BU2 sz_BU1 sz_BU.
    + Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
      Ent_decompose (0 :: nil) (0 :: nil); last by done.
      unfold Hbuf.
      Ent_LR_rewrite_eq_p 0 (* buf *).
      Ent_LR_subst_apply.
      by rewrite CaddnpA // sequiv_add_e_sc // beq_pxx bbang1.
    + rewrite /Hbuf [nth] lock.
      Ent_R_subst_con_distr.
      do 3 Ent_R_subst_apply.
      apply monotony_L.
      rewrite -lock (nth_map zero8); last by rewrite sz_BU2 sz_BU1 sz_BU.
      by Ent_monotony0.

(** __ssl &-> _minor_ver *<- (int) (__buf5 \<=e [ SSL_MINOR_VERSION_2 ]c \? __buf5 \:
          [ SSL_MINOR_VERSION_2 ]c); *)

idtac "27) mutation".

pose minver_exp := [ BU2 `_ 18 ]pc \<= [SSL_MINOR_VERSION_2 ]c \? 
                   [ BU2 `_ 18 ]pc \: [SSL_MINOR_VERSION_2 ]c : exp sigma _.

pose minver_u := si32<=phy (safe_cast_phy (ground_exp minver_exp erefl) sint erefl).

clear Hssl_in_left2.

(* NB: reuse safe case rather than zext directly *)
pose Hssl_minver := Ssl_context (zext 24 S74.client_hello)
    (si32<=phy (safe_cast_phy SSL_MAJOR_VERSION_3 sint erefl))
    minver_u mmaj0 mmin0 ses bu in_left2 md5s sha1s ciphers rb.

Hoare_seq_replace1 Hssl_majver Hssl_minver.
  Hoare_L_dup (Hbuf5 :: nil).
  Hoare_frame (Hssl_majver :: Hbuf5 :: nil) (Hssl_minver :: nil).
  apply hoare_mutation_fldp_subst_ityp with (str := _buf5) (Hstr := erefl) (e := [ BU2`_18 ]pc).
  - Ent_decompose (0 :: nil) (1 :: nil); by [apply ent_R_T | apply ent_id].
  - rewrite /=.
    Hoare_L_contract_bbang Hbuf5.
    set tmp := safe_cast _ _ _ _ _.
    eapply hoare_weak; last first.
      have He2 : @vars _ sigma _ tmp = nil by done.
      apply hoare_mutation_fldp_local_forward_ground_le with (val := mkSintLog (si32<=phy (ground_exp tmp erefl))) (He2 := He2).
      by rewrite /phylog_conv /= si32_of_phyK.
    by rewrite set_minor_ver_ssl_ctxt.

clear Hssl_majver.

(** __ssl &-> _max_major_ver *<- (int) __buf4; *)

idtac "28) mutation".

pose Hssl_reqmaj := Ssl_context (zext 24 S74.client_hello)
  (si32<=phy (safe_cast_phy SSL_MAJOR_VERSION_3 sint erefl))
  minver_u (zext 24 (BU2 `_ 17)) mmin0 ses bu in_left2 md5s sha1s ciphers rb.

Hoare_seq_replace1 Hssl_minver Hssl_reqmaj.
  Hoare_L_dup (Hbuf4 :: nil).
  Hoare_frame (Hssl_minver :: Hbuf4 :: nil) (Hssl_reqmaj :: nil).
  apply hoare_mutation_fldp_subst_ityp with (str := _buf4) (Hstr := erefl) (e := [ BU2`_17 ]pc).
  - Ent_decompose (0 :: nil) (1 :: nil); [done | by apply ent_id].
  - rewrite /=.
    Hoare_L_contract_bbang Hbuf4.
    set tmp := safe_cast _ _ _ _ _.
    eapply hoare_weak; last first.
      have He2 : @vars _ sigma _ tmp = nil by done.
      apply hoare_mutation_fldp_local_forward_ground_le with (val := mkSintLog (si32<=phy (ground_exp tmp erefl))) (He2 := He2).
      by rewrite /phylog_conv /= si32_of_phyK.
    by rewrite set_max_major_ver_sl_ctxt /tmp (@ge_cast_sint_cst_8c g sigma (BU2 `_ 17)) phy_of_si32K.

pose BU2_17 := !!( BU2 `_ 17 = S621.SSLv30_maj ).

Hoare_L_stren_by BU2_17 (Hbuf4 :: Hbuf4_majversion :: nil).
  rewrite /Hbuf4 /Hbuf4_majversion /BU2_17.
  Ent_LR_rewrite_eq_e 0 (* buf4 *).
  do 2 Ent_LR_subst_apply.
  rewrite bneg_neq_eq.
  set btmp := \b _.
  rewrite (@ground_bbang_sbang btmp Logic.eq_refl).
  apply ent_sbang_sbang.
  by rewrite gb_eq_e 2!ge_cst_e; case/eqP.

Hoare_L_contract_bbang Hbuf4 ; Hoare_L_contract_bbang Hbuf4_majversion.
rewrite {Hbuf4 Hbuf4_majversion}.
apply hoare_pullout_sbang => {}BU2_17.

clear Hssl_minver.

(** __ssl &-> _max_minor_ver *<- (int) __buf5; *)

idtac "29) mutation".

pose Hssl_reqmin := Ssl_context (zext 24 S74.client_hello)
  (si32<=phy (safe_cast_phy SSL_MAJOR_VERSION_3 sint erefl)) minver_u
  (zext 24 (BU2 `_ 17)) (zext 24 (BU2 `_ 18)) ses bu in_left2 md5s sha1s ciphers rb.

Hoare_seq_replace1 Hssl_reqmaj Hssl_reqmin.
  Hoare_L_dup (Hbuf5 :: nil).
  Hoare_frame (Hssl_reqmaj :: Hbuf5 :: nil) (Hssl_reqmin :: nil).
  apply hoare_mutation_fldp_subst_ityp with (str := _buf5) (Hstr := Logic.eq_refl) (e := [ BU2 `_ 18 ]pc).
  - Ent_decompose (0 :: nil) (1 :: nil); by [apply ent_R_T | apply ent_id].
  - rewrite /=.
    Hoare_L_contract_bbang Hbuf5.
    set tmp := safe_cast _ _ _ _ _.
    eapply hoare_weak; last first.
      have He2 : @vars _ sigma _ tmp = nil by done.
      apply hoare_mutation_fldp_local_forward_ground_le with (val := mkSintLog (si32<=phy (ground_exp tmp erefl))) (He2 := He2).
      by rewrite /phylog_conv /= si32_of_phyK.
    by rewrite set_max_minor_ver_ssl_ctxt /tmp (@ge_cast_sint_cst_8c g sigma (BU2 `_ 18)) phy_of_si32K.

clear Hssl_reqmaj.

(** _it <-* __ssl &-> _randbytes; *)

idtac "30) lookup".

pose Hit := `! \b __it \=  [ rb ]c.
Hoare_seq_ext Hit.
  Hoare_frame (Hssl_reqmin :: nil) (Hssl_reqmin :: Hit :: nil).
  apply hoare_lookup_fldp_stren, ent_R_lookup_fldp with (pv := rb).
  - by rewrite get_randbytes_ssl_ctxt /phylog_conv /= ptr_of_phyK.
  - Ent_R_subst_con_distr.
    rewrite /Hssl_reqmin /Ssl_context.
    do 2 Ent_LR_subst_apply.
    by Ent_monotony0.

(** memcpy _it erefl __it (__buf \+ [ 6 ]sc) [ 32 ]uc; *)

idtac "31) memcpy".

Hoare_seq_replace1 init_rb final_rb.
  rewrite /Hbu -(cat_take_drop 19 BU2) map_cat.
  Rewrite_Precond @mapstos_fit_cat.
    reflexivity.
    rewrite -map_cat cat_take_drop size_map sz_BU2 sz_BU1 inj_mult sz_BU sizeof_ityp; by vm_compute.
  Rewrite_Postcond @mapstos_fit_con.
    reflexivity.
    rewrite -map_cat cat_take_drop size_map sz_BU2 sz_BU1 inj_mult sz_BU sizeof_ityp; by vm_compute.
  set Hbu1 := [ bu ]c |---> _.

  rewrite size_map size_take sz_BU2 sz_BU1 sz_BU /= -(cat_take_drop '|tls_max S7412.Random| (drop 19 BU2)) map_cat.
  Rewrite_Precond @mapstos_fit_cat.
    reflexivity.
    rewrite -map_cat cat_take_drop size_map size_drop sz_BU2 sz_BU1 sz_BU sizeof_ityp; by vm_compute.
  rewrite size_map size_take size_drop sz_BU2 sz_BU1 sz_BU [Z.of_nat _]/=.
  Rewrite_Postcond @mapstos_fit_con.
    reflexivity.
    rewrite -map_cat cat_take_drop size_map size_drop sz_BU2 sz_BU1 sz_BU sizeof_ityp; by vm_compute.
  rewrite size_map size_take size_drop sz_BU2 sz_BU1 sz_BU [Z.of_nat _]/=.
  rewrite (_ : Z.abs_nat (tls_max S7412.Random) = 32); last by done.
  set Hbu2 := [ bu ]c \+ _ |---> _.
  set Hbu3 := [ bu ]c \+ _ \+ _ |---> _.
  rewrite /init_rb -(cat_take_drop '|tls_max S7412.Random| RB) map_cat.
  Rewrite_Precond @mapstos_fit_cat.
    reflexivity.
    rewrite -map_cat size_map cat_take_drop sz_RB; by vm_compute.
  rewrite size_map size_take sz_RB [Z_of_nat _]/= (_ : '| (tls_max S7412.Random) | = 32); last by done.
  set init_rb1 := [ rb ]c |---> _.
  set init_rb2 := [ rb ]c \+ [ 32 ]sc |---> _.
  rewrite /final_rb /Final_rb map_cat.
  Rewrite_Postcond @mapstos_fit_con.
    reflexivity.
    rewrite size_cat 2!size_map sizeof_ityp size_drop sz_RB [tls_max _]/= (_ : Z.abs_nat 32 = 32) //.
    apply (@leZ_ltZ_trans (Z.of_nat ((32 + (64 - 32)) * sizeof_integral uchar))).
      apply inj_le; apply/leP.
      rewrite leq_mul2r; apply/orP; right.
      rewrite leq_add2r; by apply size_slice_leq.
    by vm_compute.
  rewrite (_ : '| (tls_max S7412.Random) | = 32); last by done.
  rewrite size_map size_slice_exact; last first.
    apply leq_trans with ('| the_n_plus5 |); last by assumption.
    rewrite (_: rand + 32 = Z.abs_nat 43) //.
    apply/leP/Zabs_nat_le.
    unfold the_n_plus5; omega.
  set final_rb1 := [ rb ]c |---> _.
  set final_rb2 := [ rb ]c \+ [ 32 ]sc |---> _.
  Hoare_frame (Hbuf :: Hit :: Hbu2 :: init_rb1 :: nil)
             (Hbuf :: Hit :: Hbu2 :: final_rb1 :: nil).
    by rewrite memcpy_input_inde.
  rewrite /Hit /Hbuf /Hbu2 /init_rb1 /final_rb1.
  have -> : SI |{ rand, 32) = take 32 (drop 19 BU2).
    rewrite (_: rand = 11) // (_: take 32 (drop 19 BU2) = BU2 |{ 19, 32)) //.
    rewrite {1}(_: 11 = 5 + 6) // {2}(_: 19 = 13 + 6) //.
    apply slice_shift with (sz := '| the_n |); first by done.
    have Hthe_n2 : '| 45 | <= '| the_n | by apply/leP/Zabs_nat_le; omega.
    rewrite (_: Z.abs_nat 45 = 45) in Hthe_n2; last by done.
    by apply ltn_trans with 44.
  apply hoare_stren with (`! \b __buf \= [ bu ]c \+ [ 13 ]sc ** `! \b __it \= [ rb ]c **
     __buf \+ [ 6 ]sc |---> map phy<=ui8 (take 32 (drop 19 BU2)) **
     __it |---> map phy<=ui8 (take 32 RB)).
  Ent_LR_rewrite_eq_p 0 (* buf *).
  do 3 Ent_LR_subst_apply.
  Ent_R_subst_con_distr.
  do 4 Ent_LR_subst_apply.
  Ent_LR_rewrite_eq_p 0 (* it *).
  do 2 Ent_LR_subst_apply.
  Ent_R_subst_con_distr.
  do 4 Ent_LR_subst_apply.
  Ent_decompose (0 :: nil) (2 :: nil).
  - by rewrite CaddnpA // sequiv_add_e_sc_pos.
  - by rewrite 2! bbang_eqpxx 2!coneP.

  apply hoare_weak with (`! \b  __buf \= [ bu ]c \+ [ 13 ]sc **
     `! \b __it \= [ rb ]c ** __buf \+ [ 6 ]sc |---> map phy<=ui8 (BU2 |{ 19 , 32 )) **
     __it |---> map phy<=ui8 (BU2 |{ 19 , 32 ))).
    Ent_LR_rewrite_eq_p 0 (* buf *).
    do 3 Ent_L_subst_apply.
    Ent_R_subst_con_distr.
    do 4 Ent_R_subst_apply.
    Ent_LR_rewrite_eq_p 0. (* it *)
    do 2 Ent_L_subst_apply.
    Ent_R_subst_con_distr.
    do 4 Ent_R_subst_apply.
    Ent_decompose (0 :: nil) (2 :: nil).
      by rewrite CaddnpA // sequiv_add_e_sc_pos.
    by rewrite 2! bbang_eqpxx 2!coneP.
  Hoare_frame_idx_tmp (2 :: 3 :: nil) (2 :: 3 :: nil); first by rewrite memcpy_input_inde.
  apply memcpy_triple_cst_e => //.
    by rewrite size_map size_take size_drop sz_BU2 sz_BU1 sz_BU.
  by rewrite size_map size_take sz_RB.

(** _buf1 <-* __buf \+ [ 1 ]sc; *)

idtac "32) lookup".

pose Hbuf1 := `! \b __buf1 \= ([ BU2 `_ 14 ]pc : exp sigma (ityp: uchar)).
Hoare_seq_ext Hbuf1.
  unfold final_rb, Final_rb.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf1 :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 14) (l := map phy<=ui8 BU2) (e := [ bu ]c).
  - by rewrite size_map sz_BU2 sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  - apply ent_R_lookup_mapstos_fit_trans.
    + by rewrite size_map sz_BU2 sz_BU1 sz_BU.
    + Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
      Ent_decompose (0 :: nil) (0 :: nil); last by done.
      unfold Hbuf.
      Ent_LR_rewrite_eq_p 0 (* buf*).
      Ent_LR_subst_apply.
      by rewrite CaddnpA // sequiv_add_e_sc // beq_pxx bbang1.
    - rewrite [nth] lock.
      Ent_R_subst_con_distr.
      do 3 Ent_LR_subst_apply.
      apply monotony_L.
      rewrite -lock (nth_map zero8); last by rewrite sz_BU2 sz_BU1 sz_BU.
      by Ent_monotony0.

(** If \b __buf1 \!= [ 0 ]uc Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "33) ifte".

Hoare_ifte_bang Hbuf1_0; first by apply POLAR_ret_err.

pose BU2_14 := !!( BU2 `_ 14 = zero8 ).

Hoare_L_stren_by BU2_14 (Hbuf1 :: Hbuf1_0 :: nil).
  unfold Hbuf1, Hbuf1_0, BU2_14.
  Ent_LR_rewrite_eq_e 0 (* buf1 *).
  do 2 Ent_LR_subst_apply.
  rewrite bneq_neg_eq bnegK.
  set tmp := \b _.
  rewrite (@ground_bbang_sbang tmp Logic.eq_refl).
  apply ent_sbang_sbang.
  rewrite gb_eq_e 2!ge_cst_e; by case/eqP.

Hoare_L_contract_bbang Hbuf1 ; Hoare_L_contract_bbang Hbuf1_0.
rewrite {Hbuf1 Hbuf1_0}.
unfold BU2_14; apply hoare_pullout_sbang => {}BU2_14.

(** _buf2 <-* __buf \+ [ 2 ]sc; *)

idtac "34) lookup".

pose Hbuf2 := `! \b __buf2 \= ([ BU2 `_ 15 ]pc : exp sigma (ityp: uchar)).
Hoare_seq_ext Hbuf2.
  unfold final_rb, Final_rb.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf2 :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 15) (l := map phy<=ui8 BU2) (e := [ bu ]c).
  + by rewrite size_map sz_BU2 sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  + apply ent_R_lookup_mapstos_fit_trans.
    - by rewrite size_map sz_BU2 sz_BU1 sz_BU.
    - Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
      Ent_decompose (0 :: nil) (0 :: nil); last by done.
      unfold Hbuf.
      Ent_R_rewrite_eq_p 0 (* buf *).
      Ent_LR_subst_apply.
      by rewrite CaddnpA // sequiv_add_e_sc // bbang_eqpxx.
    - rewrite [nth] lock.
      Ent_R_subst_con_distr.
      do 3 Ent_LR_subst_apply.
      apply monotony_L.
      rewrite -lock (nth_map zero8); last by rewrite sz_BU2 sz_BU1 sz_BU.
      by Ent_monotony0.

(** _buf3 <-* __buf \+ [ 3 ]sc; *)

idtac "35) lookup".

Hoare_L_contract_bbang Hbuf3; clear Hbuf3.

pose Hbuf3 := `! \b __buf3 \= ([ BU2 `_ 16 ]pc : exp sigma (ityp: uchar)).
Hoare_seq_ext Hbuf3.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf3 :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 16) (l := map phy<=ui8 BU2) (e := [ bu ]c).
  - by rewrite size_map sz_BU2 sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  - apply ent_R_lookup_mapstos_fit_trans.
    + by rewrite size_map sz_BU2 sz_BU1 sz_BU.
    + Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
      Ent_decompose (0 :: nil) (0 :: nil); last by done.
      unfold Hbuf.
      Ent_LR_rewrite_eq_p 0 (* buf *).
      Ent_LR_subst_apply.
      by rewrite CaddnpA // sequiv_add_e_sc // bbang_eqpxx.
    - rewrite [nth] lock.
      Ent_R_subst_con_distr.
      do 3 Ent_LR_subst_apply.
      apply monotony_L.
      rewrite -lock (nth_map zero8); last by rewrite sz_BU2 sz_BU1 sz_BU.
      by Ent_monotony0.

idtac "before apply POLAR_parse_client_hello_triple2".

apply POLAR_parse_client_hello_triple2 with (BU := BU) (in_left := in_left) (BU1 := BU1) => //=.
Admitted.

Lemma POLAR_parse_client_hello_triple (BU RB ID : seq (int 8)) (CI : seq (int 32))
  (sz_BU : size BU = '| SSL_BUFFER_LEN |)
  (sz_RB : size RB = 64) (sz_ID : size ID = 32)
  (HCI : ciphers_seq CI)
  (majv0 minv0 mmaj0 mmin0 cipher0 length0 : int 32)
  (bu rb id : (:* (ityp: uchar)).-phy)
  (ses : (:* (g.-typ: ssl_session)).-phy)
  (ciphers : (:* (ityp: sint)).-phy)
  (vssl : int ptr_len)
  (md5s sha1s : 5.-tuple (int ptr_len)) :
  let init_ssl_var := `! \b __ssl \= [ phy<=ptr _ vssl ]c in
  let init_bu := [ bu ]c |---> map phy<=ui8 BU in
  let init_rb := [ rb ]c |---> map phy<=ui8 RB in
  let init_id := [ id ]c |---> map phy<=ui8 ID in
  let init_ses := ses |lV~> mk_ssl_session cipher0 length0 (ptr<=phy id) in
  let init_ciphers := [ ciphers ]c |--> map phy<=si32 CI in
  let init_ssl_context := Ssl_context (zext 24 S74.client_hello) majv0 minv0
    mmaj0 mmin0 ses bu `( 0 )_32 md5s sha1s ciphers rb in
  let final_bu := Final_bu SI bu in
  let final_ses := Final_ses SI CI ses id in
  let final_rb := Final_rb SI RB rb in
  let final_id := Final_id SI id  in
  let final_ssl_context := Ssl_context (zext 24 S74.server_hello)
    (zext 24 (SI `_ maj_ver))
    (zext 24 (if (u2Z (SI `_ min_req) <=? u2Z (S621.TLSv11_min))%Z then
              SI `_ min_req else S621.TLSv11_min))
    (zext 24 (SI `_ maj_req)) (zext 24 (SI `_ min_req ))
    ses bu `( 0 )s_32 md5s sha1s ciphers rb in
  PolarSSLAssumptions SI ->
  {{ init_ssl_var ** init_bu ** init_rb ** init_id ** init_ses ** 
     init_ciphers ** init_ssl_context }}
  ssl_parse_client_hello
  {{ error \\// (success ** !!((RecordHandshakeClientHello_decode SI).1)) **
     final_bu ** final_rb ** final_id ** final_ses **
     init_ciphers ** final_ssl_context }}.
Proof.
move=> init_ssl_var init_bu init_rb init_id init_ses init_ciphers
 init_ssl_context final_bu final_ses final_rb final_id final_ssl_context PolarAssume.
eapply hoare_weak; last by apply POLAR_parse_client_hello_triple1.
rewrite -/final_ssl_context.
apply ent_L_or; split; first by apply ent_R_or_1.
apply ent_R_or_2.
rewrite -/final_bu -/final_ses -/final_rb -/final_id -/init_ciphers.
Ent_monotony.
apply ent_sbang_sbang => H; move: H PolarAssume.
by apply PolarSSLClientHellop_decode.
Qed.

End POLAR_parse_client_hello_triple.

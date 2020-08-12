(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Div2 Even.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple.
Require Import ssrZ ZArith_ext String_ext.
Require Import ssrnat_ext seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_expr_equiv C_expr_ground C_seplog C_tactics.
Require Import rfc5246.
Import RFC5932.
Require Import POLAR_library_functions POLAR_library_functions_triple.
Require Import POLAR_ssl_ctxt POLAR_parse_client_hello POLAR_parse_client_hello_header.
Require Import POLAR_parse_client_hello_triple4.

Close Scope select_scope.

Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope seq_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope C_assert_scope.
Local Open Scope C_expr_scope.
Local Open Scope C_cmd_scope.
Local Open Scope C_value_scope.
Local Open Scope C_types_scope.

(** * Verification of the ClientHello Parsing Program (3/4) *)

Section POLAR_parse_client_hello_triple.

Variable SI : seq (int 8).

Lemma POLAR_parse_client_hello_triple3 (BU RB : seq (int 8)) (CI : seq (int 32))
  (sz_BU : size BU = '| SSL_BUFFER_LEN |)
  (HCI : ciphers_seq CI)
  (cipher0 length0 : int 32)
  (bu rb id : (:* (ityp: uchar)).-phy)
  (ses : (:* (g .-typ: ssl_session)).-phy)
  (ciphers : (:* (ityp: sint)).-phy)
  (vssl : int ptr_len)
  (md5s sha1s : 5.-tuple (int ptr_len)) :
  let init_ssl_var := `! \b __ssl \= [ phy<=ptr (POLAR_ssl_ctxt.g .-typ: ssl_context) vssl ]c in
  let init_ciphers := [ ciphers ]c |--> map phy<=si32 CI in
  let final_bu := Final_bu SI bu in
  let final_ses := Final_ses SI CI ses id in
  let final_rb := Final_rb SI RB rb in
  let final_id := Final_id SI id in
  let final_ssl_context := Ssl_context (zext 24 S74.server_hello)
    (zext 24 (SI `_ maj_ver))
    (zext 24 (if (u2Z (SI `_ min_req) <=? u2Z (S621.TLSv11_min))%Z then
              SI `_ min_req else S621.TLSv11_min))
    (zext 24 (SI `_ maj_req)) (zext 24 (SI `_ min_req ))
    ses bu `( 0 )s_32 md5s sha1s ciphers rb in
  forall BU1 : seq (int 8),
  BU1 |{ 8, 5) = SI |{ 0, 5) ->
  size BU1 = size BU ->
  forall in_left0, in_left0 = u32<=Z 5 ->
  let the_n := Z<=s ((zext 24 (BU1 `_ 11) `<< 8) `|` zext 24 (BU1 `_ 12)) in
  let the_n_plus5 := (5 + the_n)%Z in
  (45 <= the_n)%Z -> (the_n <= 512)%Z ->
  forall in_left2, in_left2 = u32<=Z the_n_plus5 ->
  forall BU2 : seq (int 8),
  let Hbu := [ bu ]c |---> map phy<=ui8 BU2 in
  BU2 |{ 8 + 5, Z.abs_nat the_n) =
    SI |{ 5, Z.abs_nat the_n) ->
  BU2 |{ 8, 5) = BU1 |{ 8, 5) ->
  size BU2 = size BU1 ->
  '| the_n_plus5 | <= size SI ->
  let Hbuf := `! \b __buf \= [ bu ]c \+ [ 13 ]sc in
  let Hn0 := `! \b __n0 \= [ in_left2 ]pc in
  let Hn_old : assert := `! \b __n_old \= [ the_n ]sc in
  let Hn := `! \b __n \= __n0 \- [ 5 ]sc in
  BU1 `_ 8 `& Z2u 8 128  = `( 0 )_8 /\ BU1 `_ 8 = S621.handshake ->
  BU2 `_ 13 = S74.client_hello ->
  BU2 `_ 17 = S621.SSLv30_maj ->
  let Hbuf5 := `! \b __buf5 \= [ BU2 `_ 18 ]pc in
  let minver_exp := [BU2 `_ 18]pc \<= [ SSL_MINOR_VERSION_2 ]c \?
              [BU2 `_ 18]pc \: [ SSL_MINOR_VERSION_2 ]c : @exp _ sigma (g.-ityp: uchar) in
  let minver_u := si32<=phy (safe_cast_phy (ground_exp minver_exp Logic.eq_refl) sint Logic.eq_refl) in
  let reqmin_sslcontext := Ssl_context (zext 24 S74.client_hello)
      (si32<=phy (safe_cast_phy SSL_MAJOR_VERSION_3 sint Logic.eq_refl))
      minver_u (zext 24 (BU2 `_ 17)) (zext 24 (BU2 `_ 18)) ses bu
      in_left2 md5s sha1s ciphers rb in
  BU1 `_ 9 = S621.SSLv30_maj ->
  BU2 `_ 14 = zero8 ->
  let Hm := `! \b __n \= [4 ]sc \+ ((int) ([ BU2 `_ 15 ]pc : exp _ (ityp: uchar)) \<< [8 ]sc \| (int) ( [ BU2 `_ 16 ]pc : exp _ (ityp: uchar))) in
  let Hsess_len := `! \b __sess_len \= (int) ([ BU2 `_ 51 ]pc : exp _ (ityp: uchar)) in
  let Hsess_len_bound := `! \~b \b __sess_len \< [ 0 ]sc \|| __sess_len \> [ 32 ]sc in
  let Hssl_session_0 := `! \b __ssl_session_0 \= [ ses ]c in
  (Z<=nat csuites.+1 + Z<=u BU2 `_ 51 < the_n_plus5)%Z ->
  let Hses_length := ses |lV~> mk_ssl_session cipher0 (zext 24 (BU2 `_ 51)) (ptr<=phy id) : assert in
  let Hssl_session_0_length := `! \b __ssl_session_0_length \= (int) ([ BU2 `_ 51 ]pc : exp _ (ityp: uchar)) in
  let Hit := `! \b __it \= [ id ]c in
  (Z<=u (BU2 `_ 51) <= 32)%Z ->
  nat<=u (BU2 `_ 51) <= 32 ->
  let Shigh := [ BU2 `_ (52 + nat<=u (BU2 `_ 51)) ]pc : exp sigma (g.-ityp: uchar) in
  let Slow := [ BU2 `_ (53 + nat<=u (BU2 `_ 51)) ]pc : exp sigma (g.-ityp: uchar) in
  let Hciph_len := `! \b __ciph_len \= ((int) Shigh \<< [ 8 ]sc \| (int) Slow) in
  let Hciph_len_bound := `! \~b \b __ciph_len \< [ 2 ]sc \|| __ciph_len \> [ 256 ]sc \|| __ciph_len \% 1 \!= [ 0 ]sc in
  let ciph_len_exp := (int) Shigh \<< [ 8 ]sc \| (int) Slow : exp sigma (ityp: sint) in
  let ciph_len_value := @ground_exp g sigma _ ciph_len_exp Logic.eq_refl in
  let ciph_len_value_Z := Z<=s (si32<=phy ciph_len_value) in
  let ciph_len_value_nat := '| ciph_len_value_Z | in
  (Z<=nat compmeth + Z<=u BU2 `_ 51 + ciph_len_value_Z < the_n_plus5)%Z ->
  (2 <= ciph_len_value_Z <= 256)%Z ->
  1 < ciph_len_value_nat <= 256 ->
  let comp_len_exp := (int) ([ BU2 `_ (54 + nat<=u (BU2 `_ 51) + ciph_len_value_nat) ]pc : exp _ (ityp: uchar)) in
  let comp_len_value := @ground_exp g sigma _ comp_len_exp (refl_equal _) in
  let Hcomp_len := `! \b __comp_len \= [ comp_len_value ]c in
  let Hextensions : assert := `! \~b
                    \b [ Z<=nat (succn compmeth) ]sc \+ __sess_len \+
                      __ciph_len \+ __comp_len \!=
                      [ 5 ]sc \+ __n_old in
  let goto_have_cipher_0 := `! \b __goto_have_cipher \= [ 0 ]sc in
  {{ goto_have_cipher_0 ** Hcomp_len ** Hciph_len ** Hit **
     Hssl_session_0_length ** Hssl_session_0 ** Hsess_len ** Hm **
     Hbuf5 ** Hn ** Hn_old ** Hn0 ** Hbuf ** Hbu ** reqmin_sslcontext ** success **
     init_ssl_var ** final_rb ** final_id ** Hses_length **
     init_ciphers ** Hsess_len_bound ** Hciph_len_bound **
     `! \~b \b __comp_len \< [ 1 ]sc \|| __comp_len \> [ 16 ]sc **
     Hextensions }}
  ssl_parse_client_hello4 ssl_parse_client_hello5
  {{ error \\//
     success ** final_bu ** final_ses ** final_rb **
     final_id ** final_ssl_context ** !!( PolarSSLClientHellop SI ) ** init_ciphers }}.
Proof.
move=> init_ssl_var init_ciphers final_bu final_ses final_rb
  final_id final_ssl_context BU1 BU1SI sz_BU1 in_left0 in_left0_5
  the_n the_n_plus5 HN1 HN0 in_left2 Hin_left2 BU2 Hbu BU2SI BU2BU1
  sz_BU2 HSI_new Hbuf Hn0 Hn_old Hn BU1_8 BU2_13 BU2_17 Hbuf5
  minver_exp minver_u reqmin_sslcontext BU1_9 BU2_14 Hm Hsess_len
  Hsess_len_bound Hssl_session_0 csuites_max Hses_length
  Hssl_session_0_length Hit BU_51 BU1_51 Shigh Slow Hciph_len
  Hciph_len_bound ciph_len_exp ciph_len_value ciph_len_value_Z
  ciph_len_value_nat compmeth_max Hciph_len_bound_Z
  Hciph_len_bound_nat comp_len_exp comp_len_value
  Hcomp_len Hextensions goto_have_cipher_0.

idtac "55) forloop".

pose Hciph_len_even := sepex k',
  !!( Z<=nat k' * 2 < 2 ^^ 30)%Z ** `! \b __ciph_len \= [ Z<=nat k' * 2 ]sc.

Hoare_L_stren_by Hciph_len_even (Hciph_len_bound :: nil).
  rewrite /Hciph_len_bound /Hciph_len_even -2!bbang_bneg_or -CgeqNlt -CleqNgt bneq_neg_eq bnegK.
  eapply ent_trans; last by apply mod_1_even_nat_gen.
  rewrite conA; apply monotony_R.
  apply monotony; [ rewrite sequiv_ge_sym; by apply b_le_trans_L | by apply b_le_trans_R ].

pose inv_outer :=
  reqmin_sslcontext ** Hbuf ** Hbu ** init_ciphers ** Hciph_len ** Hciph_len_even **
  Hsess_len ** Hses_length **
  ((`! \b __goto_have_cipher \= [ 1 ]sc **
     (sepex i, !!(i < size CI) ** sepex k, !!( k < 128 ) **
       `! \b [ Z<=nat k * 2 ]sc \< __ciph_len **
       `! \b __ssl_ciphers_i \= [ CI `32_ i ]pc **
       !!( BU2 `_ (54 + nat<=u (BU2 `_ 51) + 2 * k) = `( 0 )_ 8 ) **
       `! \b (int) __ssl_ciphers_i \= (int) ([ BU2 `_ (54 + nat<=u (BU2 `_ 51) + k * 2 + 1) ]pc : exp _ (ityp: uchar)))) \\//
   (`! \b __goto_have_cipher \= [ 0 ]sc **
      ((`! \b __ssl_ciphers_i \!= [ 0 ]sc **
        sepex i, !!(i < size CI) ** `! \b __i \= [ Z<=nat i ]sc **
                `! \b __ssl_ciphers_i \= [ CI `32_ i ]pc) \\//
       `! \b __ssl_ciphers_i \= [ 0 ]sc))).

unfold ssl_parse_client_hello4.

Hoare_seq_replace (goto_have_cipher_0 :: Hses_length :: reqmin_sslcontext :: Hbuf ::
                   Hbu :: init_ciphers :: Hciph_len :: Hsess_len :: Hciph_len_even :: nil)
                  (inv_outer :: nil); last first.

  by apply POLAR_parse_client_hello_triple4 with (BU := BU) (in_left0 := in_left0).

Hoare_frame (goto_have_cipher_0 :: Hses_length :: reqmin_sslcontext :: Hbuf ::
    Hbu :: init_ciphers :: Hciph_len :: Hsess_len :: Hciph_len_even :: nil)
  (inv_outer :: nil).

idtac "55) forloop".

(** For( _i <- [ 0 ]sc \;
    If \b __goto_have_cipher \= [ 0 ]sc Then
      _ssl_ciphers <-* __ssl &-> _ciphers;
      _ssl_ciphers_i <-* __ssl_ciphers \+ __i
    Else
      nop
    \,
   __goto_have_cipher \= [ 0 ]sc \&& __ssl_ciphers_i \!= [ 0 ]sc\;
    _i \++ ) *)

apply hoare_forloop2 with (inv := inv_outer).
- idtac "55)a) forloop entry".
  pose Hi := `! \b __i \= [ 0 ]sc.
  Hoare_seq_ext Hi.
    Hoare_frame (@nil assert) (Hi :: nil).
    apply hoare_assign_stren.
    Ent_R_subst_apply.
    by Ent_monotony0.
  apply hoare_ifte_bang; last first.
    apply (hoare_stren FF); last by apply hoare_L_F.
    set not_goto_have_cipher_0 := `! \~b _.
    by Ent_L_contradict (goto_have_cipher_0 :: not_goto_have_cipher_0 :: nil).
  Hoare_L_contract_bbang goto_have_cipher_0.
  pose H_ssl_ciphers := `! \b __ssl_ciphers \= [ ciphers ]c.
  Hoare_seq_ext H_ssl_ciphers.
    Hoare_frame (reqmin_sslcontext :: nil) (reqmin_sslcontext :: H_ssl_ciphers :: nil).
    apply hoare_lookup_fldp_stren, ent_R_lookup_fldp with (pv := ciphers).
    - by rewrite /phylog_conv /= -Eqdep.Eq_rect_eq.eq_rect_eq /= ptr_of_phyK.
    - Ent_R_subst_con_distr.
      rewrite /reqmin_sslcontext /Ssl_context; do 2 Ent_R_subst_apply.
      by Ent_monotony0.
  have size_CI : 0 < size CI by case: HCI; case=> CI' [] _ -> _; rewrite size_rcons.
  apply hoare_lookup_mapstos_stren with (i := 0) (l := map phy<=si32 CI) (e := [ ciphers ]c).
  - rewrite size_map sizeof_ityp.
    apply (@leZ_ltZ_trans (Z<=nat (size largest_ssl_default_ciphers * 4))); last by vm_compute.
    apply/leZP.
    rewrite 2!inj_mult leZ_pmul2r' // -Z_of_nat_le.
    by case: HCI.
  - apply ent_R_lookup_mapstos_trans.
    + rewrite size_map; exact size_CI.
    + Ent_decompose (6 (* init_ciphers *) :: nil) (1 (* init_ciphers *) :: nil); first by apply ent_id.
      unfold H_ssl_ciphers.
      Ent_R_rewrite_eq_p 0 (* ssl_ciphers *).
      Ent_R_subst_con_distr.
      do 2 Ent_R_subst_apply.
      unfold Hi.
      Ent_R_rewrite_eq_e 0 (* i *).
      Ent_R_subst_con_distr.
      do 2 Ent_R_subst_apply.
      apply (ent_trans TT) => //; by Ent_monotony0.
    + rewrite [nth]lock.
      unfold inv_outer.
      Ent_R_subst_con_distr.
      Ent_R_wp_assign_or.
      Ent_R_or_2.
      Ent_R_subst_con_distr.
      Ent_R_wp_assign_or.
      Ent_R_or_1.
      Ent_R_subst_con_distr.
      Ent_R_wp_assign_ex.
      Ent_R_ex O.
      Ent_R_subst_con_distr.
      Ent_R_wp_assign_sbang.
      Ent_R_remove_sbang O size_CI.
      rewrite /reqmin_sslcontext /Ssl_context; Ent_R_subst_apply; rewrite -/(Ssl_context _ _ _ _ _ _ _ _ _ _ _ _) -/reqmin_sslcontext.
      Ent_R_subst_apply; rewrite -/Hbuf.
      Ent_R_subst_apply; rewrite -/Hbu.
      Ent_R_subst_apply; rewrite -/init_ciphers.
      Ent_R_subst_apply; rewrite -/Hciph_len.
      Ent_LR_subst_inde. (* NB: Hciph_len_even is a sepex *)
      Ent_R_subst_apply; rewrite -/Hsess_len.
      Ent_R_subst_apply; rewrite -/Hses_length.
      do 4 Ent_R_subst_apply.
      rewrite -/goto_have_cipher_0.
      Ent_monotony.
      unfold Hi, H_ssl_ciphers.
      Ent_decompose (1 :: nil) (1 :: nil); first by apply ent_id.
      rewrite -lock (nth_map zero32); last by exact size_CI.
      rewrite bbang_eq_exx conPe.
      Ent_L_contract_bbang 0.
      Bbang2sbang.
      apply ent_R_sbang.
      clear -HCI.
      rewrite gb_neq.
      case: HCI; case=> CI' [] [] HCI' size_CI' -> _.
      rewrite nth_rcons size_CI'.
      move: (HCI' _ size_CI'); apply: contra.
      rewrite gb_eq_e 2!ge_cst_e.
      move/eqP/phy_of_si32_inj/eqP.
      by rewrite Z2s_Z2u_k.
- idtac "55)b) forloop exit".
  by Ent_L_contract_bbang 0.
- idtac "55)c) forloop body".

clear goto_have_cipher_0.
pose inv_inner :=
 (* fixed part*)
 reqmin_sslcontext ** Hbuf ** Hbu ** init_ciphers **
 Hciph_len ** Hciph_len_even ** Hsess_len ** Hses_length **
 (* case where cipher was found *)
 (( `! \b __goto_have_cipher \= [ 1 ]sc **
     (sepex i, !!(i < size CI) ** `! \b __i \= [ Z<=nat i ]sc **
      sepex k, !!(k < 128) **
      `! \b [ Z<=nat k*2 ]sc \< __ciph_len **
      `! \b __ssl_ciphers_i \= [ CI `32_ i ]pc **
       !!( BU2 `_ (54 + nat<=u (BU2 `_ 51) + 2 * k) = `( 0 )_ 8 ) **
       `! \b (int) __ssl_ciphers_i \=
             (int) ([ BU2 `_ (54 + nat<=u (BU2 `_ 51) + k * 2 + 1) ]pc : exp _ (ityp: uchar))))
 \\//
 (* case where cipher is not found *)
 ( `! \b __goto_have_cipher \= [0]sc **
   `! \b __ssl_ciphers_i \!= [0]sc **
    (sepex i, !!(i.+1 < size CI) ** `! \b __i \= [ Z<=nat i ]sc **
       `! \b __ssl_ciphers_i \= [ CI `32_ i ]pc) **
    (sepex k, !!(k <= 128) **
     `! \b __j \= [ Z<=nat k * 2 ]sc) **
    `! \b __j \<= __ciph_len **
    `! \b __p \= ((__buf \+ [ 41 ]sc) \+ __sess_len) \+ __j) ).
idtac "56) forloop".
(** For( _j <- [ 0 ]sc; _p <- __buf \+ [ 41 ]sc \+ __sess_len \;
     nop\,
    __goto_have_cipher \= [ 0 ]sc \&& __j \< __ciph_len\;
     nop ) *)
apply hoare_seq with inv_inner.
  apply hoare_forloop2 with (inv := inv_inner).
  + idtac "56)a) forloop entry".
    apply hoare_seq with inv_inner; last by do 2 constructor.
    Hoare_seq_ext (`! \b __j \= [ 0 ]sc).
      set H := `! \b __j \= [ 0 ]sc.
      Hoare_frame (@nil assert) (H :: nil).
      apply hoare_assign_stren.
      Ent_LR_subst_apply.
      by Ent_monotony0.
    apply hoare_assign_stren.
    unfold inv_inner, inv_outer.
    Ent_R_subst_con_distr.
    Ent_R_wp_assign_or.
    Ent_R_or_2.
    Ent_R_subst_con_distr.
    rewrite /reqmin_sslcontext /Ssl_context.
    Ent_R_subst_apply; rewrite -/(Ssl_context _ _ _ _ _ _ _ _ _ _ _ _) -/reqmin_sslcontext.
    Ent_R_subst_apply; rewrite -/Hbuf.
    Ent_R_subst_apply; rewrite -/Hbu.
    Ent_R_subst_apply; rewrite -/init_ciphers.
    Ent_R_subst_apply; rewrite -/Hciph_len.
    Ent_LR_subst_inde. (* Hciph_len_even is a sepex *)
    Ent_R_subst_apply; rewrite -/Hsess_len.
    Ent_R_subst_apply; rewrite -/Hses_length.
    Ent_R_subst_apply. (* `!b[__goto_have_cipher \= [ 0 ]sc]) *)
    Ent_R_subst_apply. (* `!b[__ssl_ciphers_i \!= [ 0 ]sc]) *)
    Ent_LR_subst_inde. (* act on a sepex *)
    Ent_LR_subst_inde. (* act on a sepex *)
    Ent_R_subst_apply. (* (`!b[__j \<= __ciph_len]) *)
    Ent_R_subst_apply. (* (`!b[__p \= __buf \+ [ 41 ]sc \+ __sess_len \+ __j]) *)
    Ent_L_dup (Hciph_len :: nil).
    Ent_monotony.
    rewrite <- bbang_and.
    (* destruction of sepor + discriminate on the first case *)
    Ent_L_or 0.
      Ent_LR_rewrite_eq_e 0 (* goto_have_cipher *).
      Ent_L_subst_apply_bbang_occ 1%nat. (* (`!b[__j \= [ 0 ]sc]) *)
      apply (ent_trans FF); last by apply ent_L_F.
      by rewrite sequiv_bop_re_sc //= bbang_0 conFP 2!conPF.
    (* destruction of sepor + discriminate on the first case *)
    Ent_L_or 0; last first.
      rewrite bneq_neg_eq.
      by Ent_L_contradict_idx (4 (* __ssl_ciphers_i = 0 *) :: 0 :: nil).
    Ent_L_ex i.
    Ent_R_ex i.
    Ent_L_sbang 0 => i_CI.
    rewrite -!conA. (* TODO: flatten? *)
    Ent_R_ex O.
    rewrite -conA. (* TODO: flatten? *)
    have Htmp : (0 <= 128)%nat by done. Ent_R_remove_sbang 1 Htmp. clear Htmp.
    rewrite -/__j. (* CHECK: simpl indesirable *)
    Ent_R_rewrite_eq_e 3 (* j *).
    Ent_R_subst_con_distr.
    do 8 Ent_R_subst_apply.
    rewrite bbang_eq_exx coneP sequiv_add_pe_0 bbang_eqpxx conPe.
    Ent_LR_rewrite_eq_e 1. (* ssl_ciphers_i *)
    do 6 Ent_LR_subst_apply.
    Ent_R_subst_con_distr.
    do 6 Ent_LR_subst_apply.
    rewrite bbang_eq_exx coneP.
    set tmp := \b _. rewrite -> (@ground_bbang_sbang tmp Logic.eq_refl) at 1.
    rewrite gb_neq gb_eq_e 2!ge_cst_e.
    apply ent_L_sbang_con.
    move=> CI_i; have {}CI_i : CI `32_ i != `( 0 )s_32 by move: CI_i; apply contra => /eqP ->.
    rewrite Z2s_Z2u_k // in CI_i.
    have H_CI : last (Z2u _ 0) CI = (Z2u _ 0).
      case: HCI; case => CI' [] _ -> _.
      rewrite last_rcons; exact CipherSuite_to_i32_NULL.
    rewrite -ltnS in i_CI.
    move: (is_not_last_of_zero_terminated _ _ _ H_CI i_CI CI_i) => ->.
    have Htmp : true by done. Ent_R_remove_sbang O Htmp. clear Htmp.
    Ent_monotony.
    Ent_L_contract_bbang 0.
    rewrite -/Shigh -/Slow -/ciph_len_exp.
    Ent_R_rewrite_eq_e 0.
    Ent_LR_subst_apply.
    Bbang2sbang.
    apply ent_R_sbang, (Zle_gb_inv _ _ [ 0 ]sc ciph_len_exp erefl erefl).
    rewrite ge_cst_e (@i32_ge_s_cst_e _ sigma) // Z2sK // -/ciph_len_value -/ciph_len_value_Z.
    clear -Hciph_len_bound_Z; lia.
  + idtac "56)b forloop exit".
    by Ent_L_contract_bbang 0.
  + idtac "56)c) forloop body".
    apply hoare_seq with inv_inner; last first.
      apply hoare_seq with inv_inner; by do 2 constructor.
    idtac "57) lookup".
    (** _p0 <-* __p; *)
    rewrite {1}/inv_inner.
    Hoare_L_or 0.
      apply (hoare_stren FF); last by apply hoare_L_F.
      rewrite <- bbang_and.
      Ent_LR_rewrite_eq_e 0 (* goto_have_cipher *).
      Ent_L_subst_apply_bbang_occ O.
      by rewrite sequiv_bop_re_sc //= bbang_0 conFP conPF.
    Hoare_L_ex 1 k.
    Hoare_L_sbang 0 => Hk.
    set Hj := `! \b __j \= [ Z<=nat k * 2 ]sc.
    set Hcond := `! \b __goto_have_cipher \= [ 0 ]sc \&& __j \< __ciph_len.
    pose p0_exp : exp sigma (_.-typ: ityp uchar) := [ BU2 `_ (54 + nat<=u (BU2 `_ 51) + 2 * k) ]pc.
    pose Hp0 := `! \b __p0 \= p0_exp.
    set Hp := `! \b __p \= __buf \+ [ 41 ]sc \+ __sess_len \+ __j.
    set Hj_ciph_len := `! \b __j \<= __ciph_len.
    Hoare_seq_ext Hp0.
      Hoare_frame (Hbu :: Hbuf :: Hp :: Hj :: Hj_ciph_len :: Hciph_len :: Hsess_len :: Hciph_len_even :: nil)
             (Hbu :: Hbuf :: Hp :: Hj :: Hj_ciph_len :: Hciph_len :: Hsess_len :: Hp0 :: Hciph_len_even :: nil).
      apply hoare_lookup_mapstos_fit_stren with (i := 54 + nat<=u (BU2 `_ 51) + 2 * k) (l := map phy<=ui8 BU2) (e := [ bu ]c).
      + rewrite size_map sizeof_ityp sz_BU2 sz_BU1 inj_mult sz_BU; by vm_compute.
      + have Htmp2 : (- 2 ^^ 31 <= 54 + Z<=u (BU2 `_ 51) + Z<=nat k * 2 < 2 ^^ 31)%Z.
          split.
            apply (@leZ_trans Z0) => //.
            apply addZ_ge0; last lia.
            apply addZ_ge0 => //; by apply min_u2Z.
          apply (@ltZ_trans (54 + 2 ^^ 8 + Z<=nat 128 * 2)%Z) => //.
          apply/ltZP.
          rewrite -2!addZA ltZ_add2l'.
          apply/ltZP/ltZ_le_add.
          + exact: max_u2Z.
          + apply/leZP; by rewrite leZ_pmul2r' // -Z_of_nat_le.
        apply ent_R_lookup_mapstos_fit_trans.
        - rewrite size_map sz_BU2 sz_BU1 sz_BU // /SSL_BUFFER_LEN.
          apply ltn_leq_trans with (54 + '| (16384 + 512 - 54 - 256) | + 2 * 128 ) => //.
          rewrite -2!addnA ltn_add2l.
          apply/ltP.
          rewrite -!plusE.
          apply plus_lt_le_compat.
            apply Nat2Z.inj_lt.
            rewrite Z_of_nat_Zabs_nat // Z_of_nat_Zabs_nat; last by apply min_u2Z.
            exact: (@leZ_ltZ_trans 32%Z).
          apply/leP; by rewrite leq_pmul2l.
        - unfold Hbu.
          Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
          unfold Hp.
          Ent_R_rewrite_eq_p 0 (* p *).
          Ent_R_subst_con_distr.
          do 2 Ent_LR_subst_apply.
          unfold Hbuf.
          Ent_R_rewrite_eq_p 0 (* buf *).
          Ent_R_subst_con_distr.
          do 2 Ent_LR_subst_apply.
          unfold Hsess_len.
          Ent_R_rewrite_eq_e 0 (* sess_len *).
          Ent_R_subst_con_distr.
          do 2 Ent_LR_subst_apply.
          unfold Hj.
          Ent_R_rewrite_eq_e 0 (* j *).
          Ent_R_subst_con_distr.
          do 2 Ent_LR_subst_apply.
          do 2 Ent_L_contract_bbang 0.
          clear -Hk Htmp2.
          rewrite eq_pC_const sequiv_intsa_uchar_sc eq_pC_const.
          have Htmp1 : (0 <= (Z<=u (BU2 `_ 51) + Z<=nat k * 2))%Z.
            apply addZ_ge0; first exact: min_u2Z.
            apply/mulZ_ge0 => //; exact/Zle_0_nat.
          rewrite CaddnpA; last 3 first.
            + rewrite sizeof_ityp [Z<=nat _]/= mul1Z.
              split; first by apply min_u2Z.
              apply: (@ltZ_trans (2 ^^ 8)) => //; exact: max_u2Z.
            + rewrite sizeof_ityp [Z<=nat _]/= mul1Z.
              split; first by apply mulZ_ge0 => //; exact: Zle_0_nat.
              move/leP/inj_le in Hk.
              rewrite (_: Z<=nat 128 = 128%Z) // in Hk.
              apply (@leZ_ltZ_trans 256%Z); [ lia | done].
            + rewrite sizeof_ityp [Z<=nat _]/= 2!mul1Z.
              split; [assumption | lia].
          rewrite sequiv_add_e_sc_pos; last 3 first.
            + by apply min_u2Z.
            + lia.
            + apply (@ltZ_trans (2 ^^ 8 + 256)%Z) => //.
              apply ltZ_le_add.
              * by apply max_u2Z.
              * move/leP/inj_le in Hk.
                rewrite (_: Z<=nat 128 = 128%Z) // in Hk; lia.
          rewrite CaddnpA; last 3 first.
            + by rewrite sizeof_ityp.
            + rewrite sizeof_ityp [sizeof_integral _]/= mul1Z.
              split; first by assumption.
              apply (@ltZ_trans (2 ^^ 8 + Z_of_nat 128 * 2)%Z) => //.
              apply ltZ_le_add; first exact: max_u2Z.
              move/leP/inj_le in Hk; lia.
            + rewrite sizeof_ityp [Z<=nat _]/= 2!mul1Z.
              split; first by lia.
              apply (@ltZ_trans (41 + 2 ^^ 8 + Z_of_nat 128 * 2)%Z) => //.
              apply/ltZP. rewrite -addZA ltZ_add2l'. apply/ltZP.
              apply ltZ_le_add; first exact: max_u2Z.
              by apply/leZP; rewrite leZ_pmul2r' // -Z_of_nat_le.
          rewrite sequiv_add_e_sc_pos => //; last by lia.
          rewrite CaddnpA; last 3 first.
            + by rewrite sizeof_ityp.
            + rewrite sizeof_ityp [sizeof_integral _]/= mul1Z; lia.
            + rewrite sizeof_ityp [sizeof_integral _]/= 2!mul1Z; lia.
          rewrite sequiv_add_e_sc_pos => //; last 2 first.
            + lia.
            + lia.
          rewrite (_ : 13 + (41 + (Z<=u (BU2 `_ 51) + Z<=nat k * 2)) =
                       Z<=nat (54 + nat<=u (BU2 `_ 51) + 2 * k) )%Z; last first.
            rewrite -(mulnC k) !inj_plus !inj_mult /u2nat Z_of_nat_Zabs_nat; [ring | by apply min_u2Z].
          rewrite beq_pxx bbang1 coneP; by apply ent_R_T.
      - unfold Hp0.
        Ent_R_subst_con_distr.
        do 7 Ent_LR_subst_inde.
        rewrite [nth] lock.
        Ent_LR_subst_apply.
        Ent_LR_subst_inde.
        rewrite -lock (nth_map zero8); last first.
          rewrite sz_BU2 sz_BU1 (_ : size BU = '|SSL_BUFFER_LEN|) // /SSL_BUFFER_LEN.
          apply leq_ltn_trans with (54 + '|2 ^^ 8| + 256); last by done.
          rewrite -2!(addnA 54) leq_add2l.
          apply leq_add; last first.
            apply/leP/Nat2Z.inj_le.
            rewrite inj_mult mulZC.
            move/leP/Nat2Z.inj_le in Hk.
            rewrite (_: Z<=nat 128 = 128%Z) // in Hk.
            rewrite (_: Z<=nat 256 = 256%Z) // (_: Z<=nat 2 = 2%Z) //; lia.
          apply ltnW.
          apply/ltP/Zabs_nat_lt.
          split; by [apply min_u2Z | apply max_u2Z].
        set lhs := nth zero8 BU2 _.
        set rhs := BU2 `_ _ .
        suff : lhs = rhs by move=> ->; Ent_monotony0.
        by rewrite /lhs /rhs {lhs rhs} /nth'.
    idtac "58) ifte".
    (** If \b __p0 \= [ 0 ]uc Then *)
    apply hoare_ifte_bang.
      idtac "60) lookup".
      (** _p1 <-* __p \+ [ 1 ]sc; *)
      pose p1_exp : exp sigma (g.-typ: ityp uchar) := [ BU2 `_ (54 + nat<=u (BU2 `_ 51) + 2 * k + 1) ]pc.
      pose Hp1 := `! \b __p1 \= p1_exp.
      Hoare_seq_ext Hp1.
        Hoare_frame (Hbu :: Hbuf :: Hp :: Hj :: Hj_ciph_len :: Hciph_len :: Hsess_len :: Hciph_len_even :: nil)
             (Hbu :: Hbuf :: Hp :: Hj :: Hj_ciph_len :: Hciph_len :: Hsess_len :: Hp1 :: Hciph_len_even :: nil).
        apply hoare_lookup_mapstos_fit_stren with (i := 54 + u2nat (BU2 `_ 51) + 2*k + 1) (l := map phy<=ui8 BU2) (e := [ bu ]c).
        + rewrite size_map sizeof_ityp sz_BU2 sz_BU1 inj_mult sz_BU; by vm_compute.
        + apply ent_R_lookup_mapstos_fit_trans.
          - rewrite size_map sz_BU2 sz_BU1 sz_BU // /SSL_BUFFER_LEN.
            apply/ltP/Nat2Z.inj_lt.
            rewrite Z_of_nat_Zabs_nat // 3!inj_plus Nat2Z.inj_mul.
            move: BU1_51 Hk.
            clear.
            rewrite (_: Z<=nat 2 = 2%Z) // (_: Z<=nat 1 = 1%Z) // (_: Z<=nat 54 = 54%Z) //.
            move=> BU1_51 /leP /inj_le Hk.
            rewrite (_: Z<=nat 128 = 128%Z) // in Hk.
            suff: (Z<=nat (nat<=u (BU2 `_ 51)) <= 32)%Z by move=> ?; lia.
            rewrite (_: 32%Z = Z<=nat 32) //; by apply inj_le; apply/leP.
          - unfold Hbu.
            Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
            unfold Hp.
            Ent_R_rewrite_eq_p 0 (* p *).
            Ent_R_subst_con_distr; do 2 Ent_LR_subst_apply.
            unfold Hbuf.
            Ent_R_rewrite_eq_p 0 (* buf *).
            Ent_R_subst_con_distr; do 2 Ent_LR_subst_apply.
            unfold Hsess_len.
            Ent_R_rewrite_eq_e 0 (* sess_len *).
            Ent_R_subst_con_distr; do 2 Ent_LR_subst_apply.
            unfold Hj.
            Ent_R_rewrite_eq_e 0 (* j *).
            Ent_R_subst_con_distr; do 2 Ent_LR_subst_apply.
            do 2 Ent_L_contract_bbang 0.
            clear -Hk BU_51.
            have Htmp : (13 + 41 + 32 + Z<=nat k * 2 + 1 < 2 ^^ 31)%Z.
              apply (@leZ_ltZ_trans (13 + 41 + 32 + 128 * 2 + 1)%Z) => //.
              apply/leZ_add2r/leZ_add2l/leZ_wpmul2r => //.
              by move/leP/inj_le in Hk.
            rewrite CaddnpA; last 3 first.
              + rewrite sizeof_ityp mul1Z; lia.
              + by rewrite sizeof_ityp mul1Z.
              + rewrite !sizeof_ityp 2!mul1Z; lia.
            rewrite eq_pC_const sequiv_intsa_uchar_sc eq_pC_const sequiv_add_e_sc_pos => //; last 2 first.
              + lia.
              + lia.
            rewrite CaddnpA; last 3 first.
              + rewrite sizeof_ityp mul1Z.
                split; by [apply min_u2Z | apply (leZ_ltZ_trans BU_51)].
              + rewrite sizeof_ityp mul1Z; lia.
              + rewrite sizeof_ityp 2!mul1Z.
                move: (min_u2Z (BU2 `_ 51)) => ?; lia.
            rewrite sequiv_add_e_sc_pos; last 3 first.
              + by apply min_u2Z.
              + lia.
              + lia.
            rewrite CaddnpA; last 3 first.
              + by rewrite sizeof_ityp.
              + rewrite sizeof_ityp mul1Z.
                move: (min_u2Z (BU2 `_ 51)) => ?; lia.
              + rewrite sizeof_ityp 2!mul1Z.
                move: (min_u2Z (BU2 `_ 51)) => ?; lia.
            rewrite sequiv_add_e_sc_pos => //; last 2 first.
              + move: (min_u2Z (BU2 `_ 51)) => ?; lia.
              + lia.
            rewrite CaddnpA; last 3 first.
              + by rewrite sizeof_ityp.
              + rewrite sizeof_ityp mul1Z.
                move: (min_u2Z (BU2 `_ 51)) => ?; lia.
              + rewrite sizeof_ityp 2!mul1Z.
                move: (min_u2Z (BU2 `_ 51)) => ?; lia.
            rewrite sequiv_add_e_sc_pos => //; last 2 first.
              + move: (min_u2Z (BU2 `_ 51)) => ?; lia.
              + lia.
            rewrite Ceqpn_add2l_sc_equiv; last 3 first.
              + congr Z.sgn.
                rewrite 3!inj_plus inj_mult /u2nat Z_of_nat_Zabs_nat; last by apply min_u2Z.
                rewrite (_ : Z<=nat 54 = 54%Z) // (_ : Z<=nat 1 = 1%Z) //; ring.
              + rewrite sizeof_ityp mul1Z.
                move: (min_u2Z (BU2 `_ 51)) => ?; lia.
              + rewrite sizeof_ityp mul1Z 3!inj_plus inj_mult /u2nat Z_of_nat_Zabs_nat; last by apply min_u2Z.
                rewrite (_ : Z<=nat 54 = 54%Z) // (_ : Z<=nat 1 = 1%Z) // (_ : Z<=nat 2 = 2%Z) //.
                move: (min_u2Z (BU2 `_ 51)) => ?; lia.
            set lhs := (_ + _)%Z.
            set rhs := Z<=nat _.
            suff -> : lhs = rhs by rewrite beq_exx bbang1 coneP.
            rewrite /rhs /lhs {rhs lhs}.
            rewrite 3!inj_plus inj_mult /u2nat Z_of_nat_Zabs_nat; last by apply min_u2Z.
            rewrite (_ : Z<=nat 54 = 54%Z) // (_ : Z<=nat 1 = 1%Z) //; ring.
          - unfold Hp1.
            Ent_R_subst_con_distr.
            do 7 Ent_LR_subst_inde.
            rewrite [nth] lock.
            Ent_R_subst_apply.
            Ent_LR_subst_inde.
            rewrite -lock (nth_map zero8); last first.
              apply/ltP/Nat2Z.inj_lt.
              rewrite sz_BU2 sz_BU1 sz_BU.
              apply (@leZ_ltZ_trans (54 + 32 + 2 * 128 + 1)%Z); last first.
                rewrite Z_of_nat_Zabs_nat; [exact/ltZP | exact/leZP].
              rewrite 3!inj_plus inj_mult (_ : Z<=nat 54 = 54%Z) // (_ : Z<=nat 2 = 2%Z) // (_ : Z<=nat 1 = 1%Z) //.
              apply/leZ_add2r/leZ_add.
                apply/leZ_add2l; rewrite Z_of_nat_Zabs_nat //; exact: min_u2Z.
              apply/leZ_wpmul2l => //.
              rewrite (_ : 128%Z = Z_of_nat 128) //; exact/inj_le/leP.
            set lhs := nth zero8 BU2 _.
            set rhs := BU2 `_ _ .
            suff -> : lhs = rhs by Ent_monotony0.
            by rewrite /lhs /rhs {lhs rhs} /nth'.
      (** If \b (int) __p1 \= __ssl_ciphers_i Then *)
      idtac "61) ifte".
      apply hoare_ifte_bang.
        (** goto_have_cipher <- [ 1 ]sc *)
        idtac "62) assign".
        apply hoare_assign_stren.
        unfold inv_inner.
        Ent_R_subst_con_distr.
        do 8 Ent_LR_subst_inde.
        Ent_R_wp_assign_or.
        Ent_R_or_1.
        Ent_R_subst_con_distr.
        Ent_LR_subst_apply.
        Ent_LR_subst_inde.
        rewrite bbang_eq_exx coneP.
        Ent_L_ex i.
        Ent_R_ex i.
        Ent_R_ex k.
        Ent_L_sbang 0 => Hi.
        Ent_L_dup (Hciph_len :: nil).
        Ent_monotony.
        rewrite /Hcond -bbang_and.
        rewrite -> (bbang_dup2 (`! \b  __j \< __ciph_len) Logic.eq_refl) at 1.
        unfold Hj.
        rewrite -> (bbang_dup2 (`! \b __j \= [ Z<=nat k * 2 ]sc) Logic.eq_refl) at 1.
        rewrite /Hciph_len -/ciph_len_exp.
        rewrite -> (bbang_dup2 (`! \b __ciph_len \= ciph_len_exp) Logic.eq_refl) at 1.
        Ent_decompose (3 (* j = 2 k*) :: 10 (* j < ciph_len *):: 12 (* ciph_len = ciph_len_exp *) :: nil (*1 :: 8 :: 10 :: nil*)) (1(*0*) (*k  <128 *) :: nil).
          Ent_LR_rewrite_eq_e 0 (* j *).
          Ent_L_subst_apply.
          do 2 Ent_LR_subst_inde.
          rewrite conC.
          Ent_LR_rewrite_eq_e 0 (* ciph_len *).
          Ent_L_subst_apply.
          do 1 Ent_LR_subst_inde.
          Bbang2sbang.
          apply ent_sbang_sbang => abs.
          rewrite ltn_neqAle Hk andbC /=.
          apply/eqP => Htmp; rewrite Htmp in abs.
          have Hyp1 : (0 <= Z<=s (si32<=phy (@ground_exp _ sigma _ [ Z<=nat 128 * 2 ]sc erefl)) < 2 ^^ 31)%Z.
            by rewrite s2Z_ge_s_cst_e.
          have Hyp2 : (0 <= Z<=s (si32<=phy (@ground_exp _ sigma _ ciph_len_exp erefl)) < 2 ^^ 31)%Z.
            clear -Hciph_len_bound_Z.
            split.
              apply (@leZ_trans 2%Z) => //.
              by case : Hciph_len_bound_Z.
            apply (@leZ_ltZ_trans 256%Z) => //.
            by case : Hciph_len_bound_Z.
          have abs' : (Z<=s (si32<=phy (@ground_exp g sigma _ ([ Z<=nat 128 * 2 ]sc) erefl)) < Z<=s (si32<=phy (@ground_exp g sigma _ ciph_len_exp erefl)))%Z.
            eapply Zlt_gb; [exact abs | exact Hyp1 | exact Hyp2].
          rewrite s2Z_ge_s_cst_e in abs'; last by done.
          have {}abs' : (256 < ciph_len_value_Z)%Z by exact abs'.
          clear -Hciph_len_bound_Z abs'.
          lia.
        rewrite [in X in _ ===> X (*i < size CI*)** _]leq_eqVlt Hi orbC.
        have Htmp : (true || (succn i == size CI)) by done. Ent_R_remove_sbang O Htmp. clear Htmp.
        Ent_L_contract_bbang 4. (*__ssl_ciphers_i *)
        Ent_L_contract_bbang 3. (* goto have cipher = 0 *)
        rewrite coneP. (* NB: la tactic precedente retire les deux occurences de
                          `!b[__j \= [ Z<=nat k * 2 ]sc], d'ou le emp *)
        Ent_L_contract_bbang 3. (* Hj_ciph_len *)
        Ent_L_contract_bbang 3. (* Hp *)
        Ent_L_contract_bbang 4. (* j < ciph_len*)
        unfold Hp1.
        Ent_LR_rewrite_eq_e 0 (* p1 *).
        do 5 Ent_LR_subst_apply.
        Ent_R_subst_con_distr.
        do 3 Ent_R_subst_apply.
        Ent_LR_rewrite_eq_e 0. (* Hp0 *)
        do 4 Ent_LR_subst_apply.
        Ent_R_subst_con_distr.
        do 3 Ent_LR_subst_apply.
        Ent_LR_rewrite_eq_e 0. (* j = k 2 *)
        do 3 Ent_LR_subst_apply.
        Ent_R_subst_con_distr.
        do 3 Ent_LR_subst_apply.
        rewrite -(Ceq_sym _ _ _ __ssl_ciphers_i).
        Ent_LR_rewrite_eq_e 1 (* ssl_ciphers_i *).
        do 2 Ent_LR_subst_apply.
        Ent_R_subst_con_distr.
        do 3 Ent_LR_subst_apply.
        apply monotony_L.
        rewrite int_int_cast mulnC bbang_eq_exx conPe.
        Bbang2sbang.
        apply ent_sbang_sbang.
        rewrite gb_eq_e 2!ge_cst_e.
        case/eqP/(@ground_exp_c_inj _ sigma _ _ _ erefl erefl); exact.

      idtac "63) assign".
      (** _j \+<- [ 2 ]sc; _p \+p<- [ 2 ]sc *)
      Hoare_seq_replace (Hj :: Hj_ciph_len :: Hcond :: Hp :: nil)
        ((`! \b __j \= [ Z<=nat (k + 1) * 2 ]sc) ::
         (`! \b __j \< __ciph_len \+ [ 2 ]sc) ::
         (`! \b __goto_have_cipher \= [ 0 ]sc \&& __j \< __ciph_len \+ [ 2 ]sc) ::
         (`! \b __p \+ [ 2 ]sc \= __buf \+ [ 41 ]sc \+ __sess_len \+ __j) :: nil).

        apply hoare_assign_stren.

        Ent_R_subst_con_distr.
        do 13 Ent_LR_subst_inde.
        do 2 Ent_LR_subst_inde.
        do 4 Ent_LR_subst_apply.
        Ent_L_dup (Hciph_len :: nil).
        rewrite /Hj /Hj_ciph_len /Hp /Hcond /Hciph_len -[in X in X ===> _] bbang_and -[in X in _ ===> X] bbang_and.
        rewrite -/__j -/__ciph_len -/__buf -/__goto_have_cipher -/__p -/__sess_len.
        Ent_monotony.
        Ent_LR_rewrite_eq_e 0 (* j *).
        (* TODO: make a lemma to remove the lmost bbang on the lhs to speedup the tactic *)
        Ent_R_subst_con_distr.
        do 8 Ent_LR_subst_apply.
        rewrite -/Shigh -/Slow -/ciph_len_value_Z -/__p -/__ciph_len -/ciph_len_exp -/__buf -/__sess_len.
        rewrite [in X in _ ===> X] conC [in X in _ ===> X] conA.
        rewrite <- bbang_dup.
        rewrite -[in X in _ ===> X] conC.
        Ent_R_rewrite_eq_p 0 (* p *).
        Ent_R_subst_con_distr.
        do 3 Ent_LR_subst_apply.
        Ent_L_contract_bbang 0.
        have Htmp : (0 <= Z<=nat k * 2 + 2 < 2 ^^ 31)%Z.
          split; first by lia.
          apply (@leZ_ltZ_trans (128 * 2 + 2)%Z) => //.
          apply/leZ_add2r/leZ_wpmul2r => //.
          rewrite (_ : 128%Z = Z_of_nat 128) //; by move/leP/Nat2Z.inj_le in Hk.
        rewrite CaddnpA; last 3 first.
          rewrite sizeof_ityp mul1Z; lia.
          by rewrite sizeof_ityp.
          by rewrite sizeof_ityp 2!mul1Z.
        rewrite beq_pxx bbang1 conPe [in X in _ ===> X ** _](@sequiv_add_e_sc_pos _ _ (Z<=nat k * 2)%Z 2%Z) // ; last 2 first.
          lia.
          move/leP/Nat2Z.inj_le in Hk.
          apply (@leZ_ltZ_trans (Z<=nat 128 * 2 + 2)%Z) => //.
          exact/leZ_add2r/leZ_wpmul2r.
        rewrite [in X in _ ===> X]inj_plus Z.mul_add_distr_r mul1Z bbang_eq_exx coneP.
        Ent_LR_rewrite_eq_e 0 (*ciph_len*).
        do 2 Ent_LR_subst_apply.
        have -> : ciph_len_exp =s [ ciph_len_value_Z ]sc.
          by rewrite /ciph_len_value_Z /ciph_len_value sequiv_s2Z_si32_of_phy.
        rewrite (@Cltn_add2r_pos g sigma) //.
        lia.
        apply (@leZ_trans 2%Z) => //.
        by case: Hciph_len_bound_Z.
        by case: Htmp.
        apply (@leZ_ltZ_trans(256 + 2)%Z) => //.
        by apply leZ_add2r, (proj2 Hciph_len_bound_Z).

    idtac "64) assign".

    apply hoare_assign_stren.
    unfold inv_inner.
    Ent_R_subst_con_distr.
    Ent_R_wp_assign_or.
    Ent_R_or_2.
    Ent_R_subst_con_distr.
    Ent_LR_subst_inde.
    Ent_R_subst_apply. rewrite -/Hbuf.
    Ent_R_subst_apply. rewrite -/Hbu.
    Ent_R_subst_apply. rewrite -/init_ciphers.
    Ent_R_subst_apply. rewrite -/Hciph_len.
    Ent_LR_subst_inde.
    Ent_R_subst_apply. rewrite -/Hsess_len.
    Ent_R_subst_apply. rewrite -/Hses_length.
    Ent_R_subst_apply.
    Ent_R_subst_apply.
    Ent_LR_subst_inde.
    Ent_LR_subst_inde.
    Ent_R_subst_apply.
    Ent_R_subst_apply.
    have Htmp : Hciph_len_even <==> Hciph_len_even ** Hciph_len_even.
      rewrite /Hciph_len_even.
      apply sepex_pure_duplicate => x.
      rewrite -[X in _ ===> X] coneP.
      apply monotony; by [apply ent_sbang_contract | apply ent_bang_contract].
    rewrite -> Htmp at 1; clear Htmp.
    Ent_L_dup (Hciph_len :: nil). (* TODO: fix Ent_L_dup to work with sepex *)
    rewrite -/__p -/__buf -/__sess_len -/__j -/(\b __p \+ [ 2 ]sc \= __buf \+ [ 41 ]sc \+ __sess_len \+ __j).
    Ent_monotony.
    unfold Hp0, Hp1.
    Ent_R_ex (k + 1).
    do 2 Ent_L_contract_bbang 0. (* p1 = p1_exp / p0 = p0_exp *)
    do 2 Ent_L_contract_bbang 2. (* p0 = 0 / p1 = ssl_ciphers_i *)
    Ent_L_contract_bbang 4. (* goto_have_cipher = 0 & j < ciph_len + 2 *)
    unfold Hciph_len, Hciph_len_even.
    Ent_LR_rewrite_eq_e 0 (* ciph_len *) .
    rewrite -/ciph_len_value_Z -/ciph_len_exp.
    Ent_L_subst_apply.
    Ent_L_ex tmp.
    rewrite -conA (wp_assign_con _ _ (!!(Z<=nat tmp * 2 < 1073741824 (* 2 ^^ 30*) )%Z)) -conA.
    Ent_L_subst_apply.
    Ent_L_subst_apply.
    Ent_L_subst_apply.
    Ent_L_subst_apply.
    Ent_R_subst_con_distr.
    Ent_R_subst_apply.
    Ent_R_subst_apply.
    Ent_R_subst_apply.
    apply ent_L_sbang_con => Htmp.
    Ent_LR_rewrite_eq_e 1 (* j *).
    Ent_L_subst_apply.
    rewrite -/Shigh -/Slow -/ciph_len_value_Z -/ciph_len_exp.
    Ent_L_subst_apply.
    rewrite -/Shigh -/Slow -/ciph_len_value_Z -/ciph_len_exp.
    Ent_R_subst_con_distr.
    Ent_R_subst_apply.
    Ent_R_subst_apply.
    Ent_R_subst_apply.
    rewrite -/Shigh -/Slow -/ciph_len_value_Z -/ciph_len_exp bbang_eq_exx coneP.
    rewrite leq_eqVlt in Hk.
    case/orP : Hk => [/eqP Hk | Hk]; last first.
      apply ent_R_sbang_con; first by rewrite addn1.
      Bbang2sbang.
      rewrite sbang_con.
      apply ent_sbang_sbang.
      case=> H1 H2.
      have Hk' : (- 2 ^ 31 <= Z<=nat (k + 1) * 2 < 2 ^ 31 )%Z.
        split; first by apply (@leZ_trans Z0) => //; lia.
        apply (@leZ_ltZ_trans (128 * 2)%Z) => //.
        apply/leZP.
        by rewrite leZ_pmul2r' // (_ : 128 = Z<=nat 128)%Z // -Z_of_nat_le addn1.
      suff H : (Z<=nat (k + 1) * 2 <= ciph_len_value_Z)%Z.
        apply: Zle_gb_inv; by rewrite s2Z_ge_s_cst_e.
      have Htmp' : (- 2 ^ 30 <= Z<=nat tmp * 2 < 2 ^ 30 )%Z.
        split; last by exact Htmp.
        apply (@leZ_trans Z0) => //; lia.
      rewrite gb_eq_e in H1.
      move/eqP in H1.
      suff H : (Z<=nat (k + 1) * 2 < ciph_len_value_Z + 2)%Z.
        have {}H1 : (exists k, ciph_len_value_Z = 2 * k)%Z.
          exists (Z<=nat tmp).
          unfold ciph_len_value_Z, ciph_len_value.
          set goal := [_]ge.
          set lhs := [_]ge in H1.
          have -> : goal = lhs by done.
          rewrite H1 s2Z_ge_s_cst_e; last first.
            split; first by apply (@leZ_trans Z0) => //;lia.
            exact: (ltZ_trans Htmp).
          exact: mulZC.
        case: H1 => k1 H1.
        rewrite H1. rewrite H1 in H. clear -H. lia.
      set lhs := [ _ * _ ]sc in H2.
      set rhs := _ \+ _ in H2.
      apply (Zlt_gb _ _ lhs rhs erefl erefl) in H2; last 2 first.
        rewrite /lhs s2Z_ge_s_cst_e; last by exact Hk'.
        split; first by apply (@leZ_trans Z0) => //; lia.
        by case: Hk'.
        rewrite /rhs si32_of_phy_gb_add_e s2Z_add;
          (rewrite -/ciph_len_value -/ciph_len_value_Z s2Z_ge_s_cst_e // ;
           clear -Hciph_len_bound_Z ; simpl expZ; lia).
      rewrite /lhs /rhs s2Z_ge_s_cst_e in H2; last by exact Hk'.
      rewrite si32_of_phy_gb_add_e s2Z_add in H2; last first.
        rewrite -/ciph_len_value -/ciph_len_value_Z s2Z_ge_s_cst_e //.
        clear -Hciph_len_bound_Z; simpl expZ; lia.
      by rewrite [in X in (_ < _ + X)%Z] s2Z_ge_s_cst_e in H2.
    Ent_L_contract_bbang 0.
    rewrite [in X in X ===> _]Hk.
    Bbang2sbang.
    apply (ent_trans FF); last by done.
    apply sbang_entails_FF.
    apply/negP.
    rewrite -gb_bneg -(ground_bexp_sem (store0 sigma)) -CgeqNlt.
    apply beval_bop_r_le_ge.
    rewrite /ciph_len_exp ground_bexp_sem -/ciph_len_exp.
    set lhs := _ \+ _.
    set rhs := [ _ ]sc.
    apply (Zle_gb_inv _ _ lhs rhs erefl erefl).
    rewrite -(ground_exp_sem (store0 sigma)) // -/ciph_len_exp si32_of_phy_binop_ne s2Z_add; last first.
      rewrite (ground_exp_sem (store0 sigma)) // -/ciph_len_value_Z si32_of_phy_sc Z2sK //.
      simpl expZ; lia.
    rewrite (ground_exp_sem (store0 sigma)) // -/ciph_len_value -/ciph_len_value_Z.
    rewrite (@s2Z_ge_s_cst_e g sigma) // (@s2Z_ge_s_cst_e g sigma) //=; lia.

  idtac "65) assign (=63)".
  (** _j \+<- [ 2 ]sc; *)
  Hoare_seq_replace (Hj :: Hp :: Hcond :: nil)
    ((`! \b __j \= [ Z<=nat (k + 1) * 2 ]sc) ::
     (`! \b __j \< __ciph_len \+ [ 2 ]sc) ::
     (`! \b __p \+ [ 2 ]sc \= __buf \+ [ 41 ]sc \+ __sess_len \+ __j) ::
     (`! \b __goto_have_cipher \= [ 0 ]sc \&& __j \< __ciph_len \+ [ 2 ]sc) :: nil).
    apply hoare_assign_stren.
    Ent_R_subst_con_distr.
    Ent_R_subst_apply; rewrite -/Hp0.
    do 2 Ent_R_subst_apply.
    Ent_LR_subst_inde.
    Ent_R_subst_apply.
    Ent_LR_subst_inde.
    Ent_R_subst_apply; rewrite -/Hbuf.
    Ent_R_subst_apply; rewrite -/Hbu.
    Ent_R_subst_apply; rewrite -/init_ciphers.
    Ent_R_subst_apply; rewrite -/Hciph_len.
    Ent_LR_subst_inde.
    Ent_R_subst_apply; rewrite -/Hsess_len.
    Ent_R_subst_apply; rewrite -/Hses_length.
    Ent_R_subst_apply.
    Ent_R_subst_apply.
    Ent_R_subst_apply.
    Ent_R_subst_apply.
    Ent_R_subst_apply.
    rewrite -> (bbang_dup2 Hciph_len erefl) at 1.
    rewrite /Hciph_len_even.
    rewrite -> (sepex_pure_duplicate (fun k' => (!!((Z<=nat k' * 2 < 2 ^^ 30)%Z)) **
                        `! \b __ciph_len \= [ Z<=nat k' * 2 ]sc)) at 1; last first.
      move=> k'.
      rewrite -(coneP emp).
      apply monotony; by [apply ent_sbang_contract | apply ent_bang_contract].
    Ent_monotony.
    unfold Hj, Hp, Hcond, Hciph_len.
    Ent_L_ex k'.
    Ent_LR_rewrite_eq_e 0 (* j *).
    Ent_L_subst_apply.
    Ent_L_subst_apply.
    do 3 Ent_L_subst_apply.
    Ent_L_subst_apply.
    rewrite -/Shigh -/Slow -/ciph_len_value_Z -/ciph_len_exp.
    Ent_R_subst_con_distr.
    do 5 Ent_R_subst_apply.
    Ent_LR_rewrite_eq_e 2. (* ciph_len *)
    do 5 Ent_L_subst_apply.
    rewrite -/Shigh -/Slow -/ciph_len_value_Z -/ciph_len_exp.
    Ent_R_subst_con_distr.
    do 5 Ent_R_subst_apply.
    Ent_R_rewrite_eq_p 0 (* p *).
    Ent_R_subst_con_distr.
    do 5 Ent_R_subst_apply.
    have Htmp : (Z<=nat k * 2 + 2 < 2 ^^ 31)%Z.
      apply (@leZ_ltZ_trans (128 * 2 + 2)%Z) => //.
      apply/leZP.
      rewrite leZ_add2r' leZ_pmul2r' // (_ : 128%Z = Z<=nat 128) //.
      exact/leZP/Nat2Z.inj_le/leP.
    rewrite {2}(@sequiv_add_e_sc_pos g sigma (Z<=nat k * 2)%Z 2%Z) => //; last by lia.
    rewrite inj_plus mulZDl mul1Z bbang_eq_exx coneP CaddnpA; last 3 first.
      rewrite sizeof_ityp mul1Z; lia.
      rewrite sizeof_ityp mul1Z; lia.
      rewrite sizeof_ityp 2!mul1Z; lia.
    rewrite bbang_eqpxx coneP -2! bbang_and -/Slow -/Shigh -/ciph_len_exp.
    Ent_L_sbang 0 => Hk'.
    Ent_L_contract_bbang 0.
    Ent_monotony.
    rewrite -bbang_dup.
    apply (ent_trans (`! \b[ Z<=nat k * 2 ]sc \< ([ Z<=nat k' * 2 ]sc : exp _ (ityp: sint)) **
       `! \b [Z<=nat k' * 2 ]sc \<= ([ 256 ]sc : exp _ (ityp: sint)))).
      apply monotony_L.
      rewrite -> bbang_sc_le_e_sbang=> //; last by rewrite /=; lia.
      set B := \b _.
      rewrite (@ground_bbang_sbang B erefl) /B {B} gb_eq_e.
      apply ent_sbang_sbang.
      move/eqP.
      set lhs := [ _ ]ge.
      set rhs := [ _ ]ge.
      move=> lhs_rhs.
      have {}lhs_rhs: Z<=s (si32<=phy lhs) = Z<=s (si32<=phy rhs) by rewrite lhs_rhs.
      rewrite s2Z_ge_s_cst_e in lhs_rhs; last by rewrite /=; lia.
      rewrite /rhs -/ciph_len_value_Z in lhs_rhs; lia.
    rewrite -> bbang_sc_lt_e_sbang; last 2 first.
      lia.
      simpl; lia.
    rewrite -> bbang_sc_le_e_sbang => //; last by simpl; lia.
    rewrite sbang_con.
    apply ent_sbang_L => {}Hk'.
    rewrite Cltn_add2r_pos //; last 3 first.
      lia.
      lia.
      simpl; lia.
    rewrite -> (@sequiv_add_e_sc_pos g sigma (Z<=nat k * 2)%Z 2%Z) => //; last by lia.
    rewrite bbang_sc_lt_e_sbang; last 2 first.
      lia.
      simpl; lia.
    rewrite -> bbang_sc_le_e_sbang; last 2 first.
      lia.
      simpl; lia.
    rewrite sbang_con.
    apply ent_R_sbang; lia.
  idtac "66) assign (=64)".
  (** _p \+p<- [ 2 ]sc *)
  apply hoare_assign_stren.
  unfold inv_inner.
  Ent_R_subst_con_distr.
  do 8 Ent_LR_subst_inde.
  Ent_R_wp_assign_or.
  Ent_R_or_2.
  Ent_R_subst_con_distr.
  do 6 Ent_LR_subst_apply.
  Ent_L_ex i.
  Ent_R_ex i.
  Ent_R_ex (k + 1).
  Ent_R_subst_con_distr.
  Ent_R_subst_con_distr.
  Ent_LR_subst_apply.
  do 4 Ent_LR_subst_apply.
  rewrite -/__i -/__j -/__p -/__ssl_ciphers_i -/__goto_have_cipher -/__ciph_len -/__buf -/__sess_len.
  rewrite -/(\b __p \+ [ 2 ]sc \= __buf \+ [ 41 ]sc \+ __sess_len \+ __j).
  set Hj' := `! \b __j \= [ _ ]sc.
  Ent_L_dup (Hciph_len :: Hj' :: nil).
  (* TODO: problem avec Ent_L_dup -> il ne duplicate que le bbang (pas les sepex) *)
  rewrite /Hciph_len_even.
  rewrite -> (sepex_pure_duplicate (fun k' => !!((Z<=nat k' * 2 < 2 ^^ 30)%Z) ** `! \b __ciph_len \= [ Z<=nat k' * 2 ]sc)) at 1; last first.
    move=> k'.
    rewrite -(conPe emp).
    apply monotony; by [apply ent_bang_contract | apply ent_bang_contract].
  Ent_monotony.
  rewrite leq_eqVlt in Hk.
  case/orP : Hk => [ /eqP Hk | Hk].
    rewrite /Hj' {Hj'} /Hj_ciph_len /Hciph_len.
    Ent_L_contract_bbang 0 (* Hp0 *).
    Ent_L_contract_bbang 3 (* \~b p0 \= _  *).
    Ent_L_contract_bbang 4. (* i < ciph_len + 2 *)
    Ent_L_contract_bbang 4 (* _ && *) .
    apply (ent_trans FF); last by apply ent_L_F.
    apply (ent_trans (`! \b __j \<= __ciph_len **
      `! \b __ciph_len \= ((int) Shigh \<< [ 8 ]sc \| (int) Slow) **
      `! \b __j \= [ Z<=nat (k + 1) * 2 ]sc)).
      Ent_monotony.
      Ent_L_ex k'.
      rewrite -(conPe emp).
      apply monotony; by [apply ent_bang_contract | apply ent_bang_contract].
    Ent_LR_rewrite_eq_e 1 (* j *).
    do 3 Ent_LR_subst_apply.
    rewrite -/Slow -/Shigh -/ciph_len_exp.
    Ent_LR_rewrite_eq_e 0 (* ciph_len *).
    do 2 Ent_LR_subst_apply.
    Bbang2sbang.
    apply sbang_entails_FF.
    rewrite -(ground_bexp_sem (store0 sigma)).
    apply/negP.
    rewrite -beval_neg_not -CgtNle sequiv_gt_sym.
    rewrite (ground_bexp_sem (store0 sigma)).
    set tmp0 := ciph_len_exp. have H1 : vars tmp0 = nil by done.
    set tmp := [ _ ]sc. have H2 : vars tmp = nil by done.
    apply Zlt_gb_inv with (H1 := H1) (H2 := H2).
    rewrite /tmp Hk s2Z_ge_s_cst_e // (_ : (_ * _ = 258)%Z) // /tmp0 -/ciph_len_value_Z.
    clear -Hciph_len_bound_Z; lia.
  Ent_L_contract_bbang 0.
  Ent_L_contract_bbang 0.
  Ent_L_ex k'.
  Ent_L_sbang 0 => Hk'.
  Ent_L_contract_bbang 0.
  Ent_L_contract_bbang 1.
  Ent_L_contract_bbang 3.
  rewrite addn1. (*Hk.*)
  Ent_R_remove_sbang O Hk.
  rewrite /Hj'.
  Ent_LR_rewrite_eq_e 0 (* ciph_len *).
  do 3 Ent_LR_subst_apply.
  Ent_LR_rewrite_eq_e 0 (* j *).
  do 2 Ent_LR_subst_apply.
  rewrite (@sequiv_add_e_sc_pos g sigma (Z<=nat k' * 2) 2) => //; last 2 first.
    lia.
    simpl; lia.
  rewrite (_ : (Z<=nat k' * 2 + 2 = Z<=nat (k' + 1) * 2)%Z); last by rewrite inj_plus mulZDl.
  clear -Hk Hk'.
  Bbang2sbang.
  apply ent_sbang_sbang => H.
  set lhs := [ Z<=nat (k + 1) * 2 ]sc.
  set rhs := [ Z<=nat k' * 2 ]sc.
  apply (Zle_gb_inv _ _ lhs rhs erefl erefl).
  rewrite 2!ge_cst_e.
  have Kk : (- 2 ^^ 31 <= Z<=nat (k + 1) * 2 < 2 ^^ 31)%Z.
    split; first by apply (@leZ_trans Z0) => //; lia.
    apply (@ltZ_trans ((Z<=nat 129) * 2)%Z) => //.
    apply/ltZP.
    by rewrite ltZ_pmul2r' // -Z_of_nat_lt ltnS addn1.
  rewrite phy_of_si32_of_Z2s; last by exact Kk.
  rewrite phy_of_si32_of_Z2s; last first.
    split; by [apply (@leZ_trans Z0) => //; lia | apply (ltZ_trans Hk')].
  apply/leZP.
  rewrite leZ_pmul2r' //.
  apply/leZP.
  set tmp1 := [ Z<=nat (k + 1) * 2 ]sc in H.
  set tmp2 := [ Z<=nat (k' + 1) * 2 ]sc in H.
  move: (Zlt_gb g sigma tmp1 tmp2 erefl erefl _ H).
  set k1 := (_ <= _ < _)%Z.
  have K1 : k1 by rewrite /k1 {k1} phy_of_si32_of_Z2s; [lia | exact Kk].
  move/(_ K1) => {K1 k1}.
  set k2 := (_ <= _ < _)%Z.
  have Kk' : (Z<=nat (k' + 1) * 2 < 2 ^^ 31)%Z.
    apply (@ltZ_trans (1073741824 + 2)%Z) => //.
    apply/ltZP.
    rewrite inj_plus mulZDl ltZ_add2r' //; exact/ltZP.
  have K2 : k2.
    rewrite /k2 {k2} phy_of_si32_of_Z2s; last first.
      split => //; apply (@leZ_trans Z0) => //; lia.
    split; [lia | exact Kk'].
  move/(_ K2) => {K2 k2}.
  rewrite phy_of_si32_of_Z2s; last by exact Kk.
  rewrite phy_of_si32_of_Z2s; last by split => //; apply (@leZ_trans Z0) => //; lia.
  move/ltZP.
  rewrite ltZ_pmul2r' // (addn1 k') Z_S.
  move/ltZP => ?; lia.

idtac "67) inner loop increment".
(** _i \++; *)

unfold inv_inner at 1.

set Ptmp := _ \\// _.
apply hoare_seq with (reqmin_sslcontext ** Hbuf ** Hbu ** init_ciphers **
     Hciph_len ** Hciph_len_even ** Hsess_len ** Hses_length **
  ((`! \b __goto_have_cipher \= [ 1 ]sc **
      (sepex i, !!(i < size CI) ** `! \b __i \= [ Z<=nat i.+1 ]sc **
       sepex k, (!!(k < 128)) **
         `! \b [ Z<=nat k * 2 ]sc \< __ciph_len **
         `! \b __ssl_ciphers_i \= [ CI `32_ i ]pc **
         (!!(BU2 `_ (54 + nat<=u BU2 `_ 51 + 2 * k) = `( 0 )_8)) **
         `! \b (int) __ssl_ciphers_i \=
               (int) ([ BU2 `_ (54 + nat<=u BU2 `_ 51 + k * 2 + 1)]pc  : exp _ (ityp: uchar)))) \\//
   `! \b __goto_have_cipher \= [ 0 ]sc ** `! \b __ssl_ciphers_i \!= [ 0 ]sc **
   (sepex i, !!(i < size CI) ** `! \b __i \= [ Z<=nat i.+1 ]sc ** `! \b __ssl_ciphers_i \= [ CI `32_ i ]pc) **
   (sepex k, (!!(k <= 128)) ** `! \b __j \= [ Z<=nat k * 2 ]sc) **
   `! \b __j \<= __ciph_len ** `! \b __p \= __buf \+ [ 41 ]sc \+ __sess_len \+ __j)).
  apply hoare_assign_stren.
  Ent_R_subst_con_distr.
  (do 8 Ent_LR_subst_inde).
  rewrite 8!conDr.
  apply ent_L_or; split.
  - Ent_R_wp_assign_or.
    Ent_R_or_1.
    Ent_R_subst_con_distr.
    Ent_R_subst_apply.
    rewrite -/__goto_have_cipher.
    Ent_monotony.
    Ent_L_ex i.
    Ent_L_ex k.
    Ent_R_subst_apply.
    Ent_R_ex i.
    Ent_R_subst_con_distr.
    do 3 Ent_R_subst_apply.
    Ent_R_ex k.
    Ent_R_subst_con_distr.
    do 5 Ent_R_subst_apply.
    rewrite -conA.
    apply ent_L_sbang_con => i_CI.
    Ent_R_remove_sbang O i_CI.
    apply monotony_R.
    Ent_R_rewrite_eq_e 0 (* i *).
    Ent_LR_subst_apply.
    rewrite sequiv_add_e_sc_pos => //; last 2 first.
      by apply Zle_0_nat.
      apply (@ltZ_trans (Z<=nat (size CI) + 1)%Z).
        apply/ltZP; by rewrite ltZ_add2r' -Z_of_nat_lt.
      apply (@leZ_ltZ_trans (Z<=nat (size largest_ssl_default_ciphers) + 1)%Z) => //.
      apply/leZP.
      rewrite leZ_add2r' -Z_of_nat_le.
      by case: HCI.
    rewrite Z_S bbang_eq_exx; by apply ent_id.
  - Ent_R_wp_assign_or.
    Ent_R_or_2.
    Ent_R_subst_con_distr.
    do 6 Ent_R_subst_apply.
    Ent_L_ex i.
    Ent_L_ex k.
    Ent_R_ex i.
    Ent_R_subst_con_distr.
    do 3 Ent_R_subst_apply.
    (* TODO: Ent_R_flat.*)
    rewrite -2![in X in _ ===> X] conA.
    Ent_R_ex k.
    Ent_R_subst_con_distr.
    do 2 Ent_LR_subst_apply.
    rewrite -/__j -/__i -/__ssl_ciphers_i -/__goto_have_cipher -/__p -/__ciph_len -/__buf -/__sess_len.
    Ent_monotony.
    clear -HCI.
    apply ent_L_sbang_con => i_CI.
    rewrite (ltn_trans (ltnSn i) i_CI).
    have Htmp : true by done. Ent_R_remove_sbang O Htmp. clear Htmp.
    Ent_R_rewrite_eq_e O.
    Ent_LR_subst_apply.
    rewrite sequiv_add_e_sc_pos => //; last 2 first.
      by apply Zle_0_nat.
      apply (@ltZ_trans (Z<=nat (size CI))%Z).
        rewrite -Z_S; apply/ltZP; by rewrite -Z_of_nat_lt.
      apply (@leZ_ltZ_trans (Z<=nat (size largest_ssl_default_ciphers))%Z) => //.
      apply/leZP; rewrite -Z_of_nat_le.
      by case: HCI.
    rewrite -Z_S bbang_eq_exx; by apply ent_id.

pose H_ssl_ciphers_ := `! \b __ssl_ciphers \= [ ciphers ]c.

idtac "68) ifte".
(** If \b __goto_have_cipher \= [ 0 ]sc Then *)

rewrite !conDr.
apply hoare_L_or.
- (* goto have cipher = 1 *)
  apply hoare_ifte_bang.
  + apply (hoare_stren FF); last by apply hoare_L_F.
    apply (ent_trans (FF ** TT)); last by rewrite conFP.
    Ent_decompose (8 :: 10 :: nil) (0 :: nil); last by apply ent_R_T.
    Ent_LR_rewrite_eq_e 0 (* gotohavecipher *).
    do 2 Ent_LR_subst_apply.
    rewrite sequiv_bop_re_sc //= bbang_0; by apply ent_id.
  + apply skip_hoare.
    rewrite /inv_outer ![in X in _ ===> X] conDr.
    apply ent_R_or_1.
    Ent_monotony.
    Ent_L_ex i.
    Ent_R_ex i.
    by apply ent_L_con_bbang, monotony_L, ent_L_bbang_con, ent_id.
- (* goto have cipher = 0 *)
  apply hoare_ifte_bang; last by Hoare_L_contradict (8 (* goto_have_cipher = 0 *) :: 14 (* != 0 *) :: nil).

idtac "69) lookup".
(** _ssl_ciphers <-* __ssl &-> _ciphers; *)
  Hoare_seq_ext H_ssl_ciphers_.
    Hoare_frame (reqmin_sslcontext :: nil) (reqmin_sslcontext :: H_ssl_ciphers_ :: nil).
    apply hoare_lookup_fldp_stren, ent_R_lookup_fldp with (pv := ciphers).
    - by rewrite get_ciphers_ssl_ctxt /phylog_conv /= ptr_of_phyK.
    - Ent_R_subst_con_distr.
      rewrite /reqmin_sslcontext /Ssl_context.
      do 2 Ent_LR_subst_apply.
      by Ent_monotony0.

  idtac "70) lookup".
  (** _ssl_ciphers_i <-* __ssl_ciphers \+ __i *)

  unfold inv_outer.
  rewrite ![in X in {{ _ }} _ {{ X }}] conDr.
  Hoare_L_ex 0 i.
  rewrite -conA. apply hoare_pullout_sbang => i_CI.
  apply hoare_R_or_2.
  have Hhelper1 : (Z<=nat (size (map (@phy_of_si32 g) CI) * sizeof (g.-ityp: sint)) < 2 ^^ 31)%Z.
    rewrite size_map sizeof_ityp //.
    apply (@leZ_ltZ_trans (Z<=nat (size largest_ssl_default_ciphers * sizeof_integral sint))); last by done.
    rewrite 2!inj_mult.
    apply/leZP; rewrite leZ_pmul2r' // -Z_of_nat_le; by case: HCI.
  case/boolP : ((CI `32_ i.+1) == zero32) => CI_i_plus_1.
  - (* the last one is  O_32 *)
    apply hoare_R_or_2.
    Hoare_L_ex 0 k.
    rewrite -conA. apply hoare_pullout_sbang => Hk.
    apply hoare_lookup_mapstos_stren with (i := i.+1) (l := map phy<=si32 CI) (e := [ ciphers ]c).
    - exact Hhelper1.
    - set P := _ ** _.
      apply (ent_trans (!!( CI `32_ i != zero32) ** P)).
        unfold P at 1.
        rewrite -> (bbang_dup2 (`! \b __ssl_ciphers_i \= [ CI `32_ i ]pc) Logic.eq_refl) at 1.
        rewrite -> (bbang_dup2 (`! \b __ssl_ciphers_i \!= [ 0 ]sc) Logic.eq_refl) at 1.
        Ent_decompose (2 :: 14 :: nil) (O :: nil).
        + Ent_LR_rewrite_eq_e 0 (* ssl_ciphers_i *).
          do 2 Ent_LR_subst_apply.
          Bbang2sbang.
          apply ent_sbang_sbang.
          rewrite gb_neq.
          apply: contra.
          move/eqP => ->.
          by rewrite -(ground_bexp_sem (store0 sigma)) beval_eq_e_eq /zero32 -Z2s_Z2u_k.
        + by apply ent_id.
      apply ent_L_sbang_con => CI_i.
      unfold P => {P}.
      apply ent_R_lookup_mapstos_trans.
      + rewrite size_map.
        apply is_not_last_of_zero_terminated with zero32 => //.
        case: HCI; case=> CI' [] _ -> _; rewrite last_rcons; exact CipherSuite_to_i32_NULL.
      + Ent_decompose (7 (* init_ciphers*) :: nil) (1 (* cipehrs0 |--> _ *):: nil).
        + by apply ent_id.
        + unfold H_ssl_ciphers_.
          Ent_decompose (1 (* i = i+1*) :: 3 (* sslciphers = cipers0 *) :: nil) (0 (* ssl_ciphers + i = ciphers0 + i+1 *):: nil).
          Ent_R_rewrite_eq_e O.
          Ent_LR_subst_apply.
          rewrite -/__ssl_ciphers.
          Ent_R_rewrite_eq_p O.
          Ent_LR_subst_apply.
          by Ent_monotony0.
          by apply ent_R_T.
      + rewrite [nth]lock.
        Ent_R_subst_con_distr.
        rewrite {2}/reqmin_sslcontext /Ssl_context.
        Ent_R_subst_apply.
        rewrite -/(Ssl_context _ _ _ _ _ _ _ _ _ _ _ _) -/reqmin_sslcontext.
        do 4 Ent_R_subst_apply; rewrite -/Hbuf -/Hbu -/init_ciphers -/Hciph_len.
        Ent_LR_subst_inde.
        do 4 Ent_R_subst_apply; rewrite -/Hsess_len -/Hses_length.
        Ent_monotony.
        repeat apply ent_L_bbang_con.
        apply ent_L_bbang.
        clear -CI_i_plus_1 HCI i_CI CI_i.
        rewrite /nth' in CI_i_plus_1.
        rewrite  -lock (nth_map zero32); last first.
          apply is_not_last_of_zero_terminated with zero32 => //.
          case: HCI; case=> CI' [] _ -> _; rewrite last_rcons; exact CipherSuite_to_i32_NULL.
        move/eqP : CI_i_plus_1 => ->.
        rewrite /zero32 -Z2s_Z2u_k //.
        by Ent_monotony0.
  - (* the last one is not O_32 *)
    apply hoare_R_or_1.
    Hoare_L_ex 0 k.
    rewrite -conA. apply hoare_pullout_sbang => Hk.
    apply hoare_lookup_mapstos_stren with (i := i.+1) (l := map phy<=si32 CI) (e := [ ciphers ]c).
    - exact Hhelper1.
    - set P := _ ** _.
      apply (ent_trans (!!( CI `32_ i != zero32) ** P)).
        unfold P at 1.
        rewrite -> (bbang_dup2 (`! \b __ssl_ciphers_i \= [ CI `32_ i ]pc) erefl) at 1.
        rewrite -> (bbang_dup2 (`! \b __ssl_ciphers_i \!= [ 0 ]sc) erefl) at 1.
        Ent_decompose (2 :: 14 :: nil) (O :: nil).
        + Ent_LR_rewrite_eq_e 0 (* ssl_ciphers_i *) .
          do 2 Ent_LR_subst_apply.
          Bbang2sbang.
          apply ent_sbang_sbang.
          rewrite gb_neq.
          apply: contra.
          move/eqP => ->.
          rewrite -(ground_bexp_sem (store0 sigma)).
          by rewrite beval_eq_e_eq /zero32 -Z2s_Z2u_k.
        + by apply ent_id.
      apply ent_L_sbang_con => CI_i.
      unfold P => {P}.
      apply ent_R_lookup_mapstos_trans.
      + rewrite size_map.
        apply is_not_last_of_zero_terminated with zero32 => //.
        case: HCI; case=> CI' [] _ -> _; rewrite last_rcons; exact CipherSuite_to_i32_NULL.
      + Ent_decompose (7 (* init_ciphers *) :: nil) (1 :: nil).
        + by apply ent_id.
        + unfold H_ssl_ciphers_.
          Ent_decompose (1 (* i = i.+1 *) :: 3 (* ssl_ciphers = ciphers0 *) :: nil) (0 :: nil).
          Ent_R_rewrite_eq_e O.
          Ent_LR_subst_apply.
          rewrite -/__ssl_ciphers.
          Ent_R_rewrite_eq_p O. (* ssl_ciphers_i *)
          Ent_LR_subst_apply.
          by Ent_monotony0.
          by apply ent_R_T.
      + rewrite [nth]lock.
        Ent_R_subst_con_distr.
        rewrite {2}/reqmin_sslcontext /Ssl_context.
        Ent_R_subst_apply.
        rewrite -/(Ssl_context _ _ _ _ _ _ _ _ _ _ _ _) -/reqmin_sslcontext.
        do 4 Ent_R_subst_apply; rewrite -/Hbuf -/Hbu -/init_ciphers -/Hciph_len.
        Ent_LR_subst_inde.
        do 3 Ent_R_subst_apply; rewrite -/Hsess_len -/Hses_length.
        Ent_LR_subst_apply.
        Ent_LR_subst_apply.
        Ent_R_ex (S i).
        Ent_R_subst_con_distr.
        do 3 Ent_R_subst_apply.
        rewrite -/__i.
        Ent_monotony.
        repeat apply ent_L_bbang_con.
        apply ent_L_bbang.
        clear -CI_i_plus_1 HCI i_CI CI_i.
        rewrite /nth' in CI_i_plus_1.
        rewrite -lock (nth_map zero32); last first.
          apply is_not_last_of_zero_terminated with zero32 => //.
          case: HCI; case=> CI' [] _ -> _; rewrite last_rcons; exact CipherSuite_to_i32_NULL.
        have not_last : i.+1 != size CI.
          move: CI_i_plus_1; apply: contra.
          move/eqP => ->.
          by rewrite nth_default.
        rewrite ltn_neqAle not_last.
        Ent_R_remove_sbang O i_CI.
        rewrite bbang_eq_exx conPe.
        Bbang2sbang.
        apply ent_R_sbang.
        rewrite -(ground_bexp_sem (store0 sigma)) beval_neq_not_eq.
        move: CI_i_plus_1; apply: contra.
        move/eqP/phy_of_si32_inj/eqP.
        by rewrite Z2s_Z2u_k.
Qed.

End POLAR_parse_client_hello_triple.

(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Div2 Even.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
From mathcomp Require Import tuple.
Require Import ssrZ ZArith_ext String_ext ssrnat_ext seq_ext machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_expr_equiv C_expr_ground.
Require Import C_seplog C_tactics.
Require Import rfc5246.
Import RFC5932.
Require Import POLAR_library_functions POLAR_library_functions_triple.
Require Import POLAR_ssl_ctxt POLAR_parse_client_hello POLAR_parse_client_hello_header.

Close Scope select_scope.

Local Open Scope nat_scope.
Local Open Scope string_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope seq_ext_scope.
Local Open Scope C_assert_scope.
Local Open Scope C_expr_scope.
Local Open Scope C_cmd_scope.
Local Open Scope C_value_scope.
Local Open Scope C_types_scope.
Local Open Scope POLAR_scope.

(** * Verification of the ClientHello Parsing Program (2/4) *)

Section POLAR_parse_client_hello_triple.

Variable SI : seq (int 8).

Lemma POLAR_parse_client_hello_triple2 (BU RB ID : seq (int 8)) (CI : seq (int 32))
  (sz_BU : size BU = '| SSL_BUFFER_LEN |)
  (sz_ID : size ID = 32)
  (HCI : ciphers_seq CI)
  (cipher0 length0 : int 32)
  (bu rb id : (:* (ityp: uchar)).-phy)
  (ses : (:* (g.-typ: ssl_session)).-phy)
  (ciphers : (:* (ityp: sint)).-phy)
  (vssl : int ptr_len)
  (md5s sha1s : 5.-tuple (int ptr_len))  :
  let init_ssl_var := `! \b __ssl \= [ phy<=ptr _ vssl ]c in
  let init_id := [ id ]c |---> map phy_of_ui8 ID in
  let init_ses := ses |lV~> mk_ssl_session cipher0 length0 (ptr<=phy id) in
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
  forall BU1, BU1 |{ 8, 5) = SI |{ 0, 5) -> size BU1 = size BU ->
  4 < size SI ->
  forall in_left, in_left = Z2u 32 5 ->
  let the_n := Z<=s ((zext 24 (BU1 `_ 11) `<< 8) `|` zext 24 (BU1 `_ 12)) in
  let the_n_plus5 := (5 + the_n)%Z in
  (45 <= the_n)%Z -> (the_n <= 512)%Z ->
  forall in_left2, in_left2 = Z2u 32 the_n_plus5 ->
  forall BU2 : seq (int 8),
  let Hbu := [ bu ]c |---> map phy_of_ui8 BU2 in
  BU2 |{ 8 + 5, Z.abs_nat the_n) = SI |{ 5, Z.abs_nat the_n) ->
  BU2 |{ 8, 5) = BU1 |{ 8, 5) ->
  size BU2 = size BU1 ->
  '| the_n_plus5 | <= size SI ->
  let Hbuf := `! \b __buf \= [ bu ]c \+ [ 13 ]sc in
  let Hn0 := `! \b __n0 \= [ in_left2 ]pc in
  let Hn_old := `! \b __n_old \= [ the_n ]sc in
  let Hn := `! \b __n \= __n0 \- [ 5 ]sc in
  BU1 `_ 8 `& Z2u 8 128  = Z2u 8 0 /\ BU1 `_ 8 = S621.handshake ->
  BU2 `_ 13 = S74.client_hello ->
  BU2 `_ 17 = S621.SSLv30_maj ->
  let Hbuf5 := `! \b __buf5 \= ([BU2 `_ 18]pc : exp sigma (ityp: uchar)) in
  let minver_exp := [BU2 `_ 18]pc \<= [ SSL_MINOR_VERSION_2 ]c \?
                    [BU2 `_ 18]pc \: [ SSL_MINOR_VERSION_2 ]c : exp sigma (g.-ityp: uchar) in
  let minver_u := si32<=phy (safe_cast_phy (ground_exp minver_exp Logic.eq_refl) sint Logic.eq_refl) in
  let reqmin_sslcontext := Ssl_context (zext 24 S74.client_hello)
      (si32<=phy (safe_cast_phy SSL_MAJOR_VERSION_3 sint Logic.eq_refl)) minver_u
      (zext 24 (BU2 `_ 17)) (zext 24 (BU2 `_ 18)) ses bu in_left2 md5s sha1s
      ciphers rb in
  let Hit := `! \b __it \= [ rb ]c in
  BU1 `_ 9 = S621.SSLv30_maj ->
  BU2 `_ 14 = zero8 ->
  let Hbuf2 := `! \b __buf2 \= [BU2 `_ 15]pc in
  let Hbuf3 := `! \b __buf3 \= [BU2 `_ 16]pc in
  {{ Hbuf3 ** Hbuf2 ** Hit ** Hbuf5 ** Hn ** Hn_old ** Hn0 ** Hbuf **
     Hbu ** reqmin_sslcontext ** success ** init_ssl_var ** final_rb **
     init_id ** init_ses ** init_ciphers }}
  ssl_parse_client_hello3 (ssl_parse_client_hello4 ssl_parse_client_hello5)
  {{ error \\//
     success ** final_bu ** final_ses ** final_rb **
     final_id ** final_ssl_context ** !!( PolarSSLClientHellop SI ) ** init_ciphers }}.
Proof.
move=> init_ssl_var init_id init_ses init_ciphers final_bu
  final_ses final_rb final_id final_ssl_context BU1 BU1SI sz_BU1 size_SI
  in_left in_left_5 the_n the_n_plus5 HN1 HN2 in_left2 Hin_left2 BU2
  Hbu BU2SI BU2BU1 sz_BU2 HSI_new Hbuf Hn0 Hn_old Hn BU1_8 BU2_13
  BU2_17 Hbuf5 minver_exp minver_u reqmin_sslcontext Hit BU1_9 BU2_14 Hbuf2
  Hbuf3.

unfold ssl_parse_client_hello3.

(** If \b __n \!= [ 4 ]sc \+ ((int) __buf2 \<< [ 8 ]sc \| (int) __buf3) Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; ret *)

idtac "36) ifte".

Hoare_ifte_bang Hm_old; first by apply POLAR_ret_err.

pose Hm := `! \b __n \= [4 ]sc \+
  ((int) ([ BU2 `_ 15 ]pc : exp sigma (ityp: uchar)) \<< [8 ]sc \|
  (int) ([ BU2 `_ 16 ]pc : exp sigma (ityp: uchar))).

Hoare_L_stren_by Hm (Hbuf2 :: Hbuf3 :: Hm_old :: nil).
  unfold Hm, Hbuf2, Hbuf3, Hm_old.
  Ent_LR_rewrite_eq_e 0 (* buf3 *).
  do 2 Ent_L_subst_apply; Ent_R_subst_apply.
  Ent_LR_rewrite_eq_e 0 (* buf2 *).
  Ent_R_subst_apply; Ent_L_subst_apply.
  rewrite bneg_neq_eq; by apply ent_id.

Hoare_L_contract_bbang Hbuf2.
Hoare_L_contract_bbang Hbuf3.
Hoare_L_contract_bbang Hm_old.
clear Hbuf2 Hbuf3 Hm_old.

(** _buf38 <-* __buf \+ [ 38 ]sc; *)

idtac "37) lookup".

(* 51 = 8 + 5 + 38 *)
pose Hbuf38 := `! \b __buf38 \= ([ BU2 `_ 51 ]pc : exp sigma (ityp: uchar)).
Hoare_seq_ext Hbuf38.
  Hoare_frame (Hbu :: Hbuf :: nil) (Hbu :: Hbuf :: Hbuf38 :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 51) (l := map phy_of_ui8 BU2) (e := [ bu ]c).
  - by rewrite size_map sz_BU2 sz_BU1 sz_BU inj_mult Z_of_nat_Zabs_nat.
  - apply ent_R_lookup_mapstos_fit_trans.
    + by rewrite size_map sz_BU2 sz_BU1 sz_BU.
    + Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
      Ent_decompose (0 :: nil) (0 :: nil); last by [].
      unfold Hbuf.
      Ent_LR_rewrite_eq_p 0 (* buf *).
      Ent_R_subst_apply.
      Bbang2sbang.
      Ent_R_sbang 0; last by [].
      Rewrite_ground_bexp @CaddnpA => //=.
      Rewrite_ground_bexp @sequiv_add_e_sc => //=.
      by rewrite gb_eq_p.
    + rewrite [nth] lock.
      Ent_R_subst_con_distr.
      do 3 Ent_R_subst_apply.
      apply monotony_L.
      rewrite -lock (nth_map zero8); last by rewrite sz_BU2 sz_BU1 sz_BU.
      by Ent_monotony0.

(** _sess_len <- (int) __buf38; *)

idtac "38) assign".

pose Hsess_len := `! \b __sess_len \= (int) ([ BU2 `_ 51 ]pc : exp _ (ityp: uchar)).
Hoare_seq_ext Hsess_len.

  Hoare_L_dup (Hbuf38 :: nil).
  Hoare_frame (Hbuf38 :: nil) (Hsess_len :: nil).
  apply hoare_assign_stren.
  Ent_R_subst_apply.
  unfold Hbuf38.
  Ent_R_rewrite_eq_e 0 (* buf38 *).
  Ent_R_subst_apply.
  by Ent_monotony0.

Hoare_L_contract_bbang Hbuf38; clear Hbuf38.

(** If \b __sess_len \< [ 0 ]sc \|| __sess_len \> [ 32 ]sc
    \|| [ Z<=nat 45 ]sc \+ __sess_len \>= [ 5 ]sc \+ __n_old
    Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "39) ifte".

apply hoare_ifte_bang; first by apply POLAR_ret_err.

rewrite -bbang_bneg_or.
set Hsess_len_2 := `! \~b \b __sess_len \< [0 ]sc \|| __sess_len \> [ 32 ]sc.
set Hsess_len_3 := `! \~b \b [ Z<=nat csuites.+1 ]sc \+ __sess_len \>= [ 5 ]sc \+ __n_old.

(** _ssl_session_0 <-* __ssl &-> _session; *)

idtac "40) lookup".

pose Hssl_session_0 := `! \b __ssl_session_0 \= [ ses ]c.

Hoare_seq_ext Hssl_session_0.
  Hoare_frame (reqmin_sslcontext :: nil) (reqmin_sslcontext :: Hssl_session_0 :: nil).
  apply hoare_lookup_fldp_stren, ent_R_lookup_fldp with (pv := ses).
  - by rewrite get_session_ssl_ctxt /phylog_conv /= ptr_of_phyK.
  - Ent_R_subst_con_distr. (* 1 *)
    rewrite /reqmin_sslcontext /Ssl_context.
    do 2 Ent_R_subst_apply.
    by Ent_monotony0.

pose Hsess_len3'' := !!(Z<=nat csuites.+1 + Z<=u BU2 `_ 51 < the_n_plus5)%Z.
Hoare_L_stren_by Hsess_len3'' (Hsess_len :: Hn_old :: Hsess_len_3 :: nil).
  unfold Hsess_len, Hsess_len_3, Hn_old.
  Ent_LR_rewrite_eq_e 0 (* sess_len *).
  do 2 Ent_L_subst_apply; Ent_R_subst_apply.
  fold Hsess_len3''.
  Ent_LR_rewrite_eq_e 0 (* n_old *).
  Ent_R_subst_apply; Ent_L_subst_apply.
  Bbang2sbang.
  apply ent_sbang_sbang.
  rewrite gb_bneg_bop_r_ge.
  move/Zlt_gb. move/(_ erefl erefl).
  rewrite si32_of_phy_gb_add_e i32_ge_s_cst_e ge_cast_sint_cst_8c phy_of_si32K.
  rewrite si32_of_phy_gb_add_e 2!i32_ge_s_cst_e.
  have H1 : (0 <= Z<=nat csuites.+1 + Z<=u BU2 `_ 51 < 2 ^^ 31)%Z.
    split.
      apply (@leZ_trans (45%Z + Z0)%Z) => //; exact/leZ_add2l/min_u2Z.
    apply (@ltZ_trans (45%Z + 2 ^^ 8)%Z) => //; exact/ltZ_add2l/max_u2Z.
  rewrite s2Z_add; last first.
    rewrite Z2sK; last by [].
    rewrite (s2Z_zext 24) //.
    split; last by case: H1.
    apply (@leZ_trans Z0) => //; by case: H1.
  rewrite Z2sK // s2Z_add; last first.
    rewrite Z2sK //.
    clear -HN1 HN2.
    rewrite Z2sK; last by simpl expZ; omega.
    simpl expZ; omega.
  rewrite Z2sK // Z2sK; last by simpl expZ; omega.
  rewrite (s2Z_zext 24) //.
  apply.
  exact H1.
  simpl expZ; omega.

Hoare_L_contract_bbang Hsess_len_3; clear Hsess_len_3.
apply hoare_pullout_sbang => Hsess_len_3'.
clear Hsess_len3''.

(** __ssl_session_0 &-> _length *<- __sess_len; *)

idtac "41) mutation".

pose Hses_length := ses |lV~> mk_ssl_session cipher0 (zext 24 (BU2 `_ 51)) (ptr<=phy id) : assert.

Hoare_seq_replace1 init_ses Hses_length.
  Hoare_L_dup (Hsess_len :: Hssl_session_0 :: nil).
  Hoare_frame (init_ses :: Hsess_len :: Hssl_session_0 :: nil) (Hses_length :: nil).
  unfold init_ses, Hses_length, mk_ssl_session.
  set ses_hdr_pre := mk_ssl_sess_logs _ _ _.
  set ses_hdr_post := mk_ssl_sess_logs _ _ _.
  apply hoare_mutation_fldp_subst_ptr with (str := _ssl_session_0) (Hstr := Logic.eq_refl) (e'' := [ ses ]c).
  - Ent_decompose (0 :: 1 :: nil) (1 :: nil); by [| apply ent_id].
  - rewrite /=.
    apply hoare_mutation_fldp_subst_ityp with (str := _sess_len) (Hstr := Logic.eq_refl) (e := (int) ([ BU2`_51 ]pc : exp sigma (ityp: uchar))).
    + Ent_decompose (0 :: 2 :: nil) (1 :: nil); by [| apply ent_id].
    + rewrite /=.
      Hoare_L_contract_bbang Hsess_len; Hoare_L_contract_bbang Hssl_session_0.
      set tmp := safe_cast _ _ _ _ _.
      eapply hoare_weak; last first.
        have He2 : @vars _ sigma _ tmp = nil by [].
        apply hoare_mutation_fldp_local_forward_ground_lV with (val := mkSintLog (zext 24 (BU2`_51))) (He2 := He2).
        by rewrite /phylog_conv /= /tmp ge_cast_sint_cst_8c.
      rewrite /= -!Eqdep.Eq_rect_eq.eq_rect_eq /ses_hdr_post /mk_ssl_sess_logs /tmp; by apply ent_id.

(** _it <-* __ssl_session_0 &-> _id; *)

idtac "42) lookup".

Hoare_L_contract_bbang Hit; clear Hit.

pose Hit := `! \b __it \= [ id ]c.
Hoare_seq_ext Hit.
  Hoare_L_dup (Hssl_session_0 :: nil).
  Hoare_frame (Hses_length :: Hssl_session_0 :: nil) (Hses_length :: Hit :: nil).
  apply (hoare_lookup_fldp_subst _ _ssl_session_0 erefl ([ ses ]c)).
  - Ent_decompose (0 :: nil) (1 :: nil); by [apply ent_R_T | apply ent_id].
  - rewrite /=.
    Hoare_L_contract_bbang Hssl_session_0.
    apply hoare_lookup_fldp_stren.
    unfold Hses_length, mk_ssl_session.
    set ses_hdr := mk_ssl_sess_logs _ _ _.
    apply ent_R_lookup_fldp_trans with (pv := id) (lvs := ses_hdr).
    + by apply ent_R_con_T.
    + by rewrite /= -Eqdep.Eq_rect_eq.eq_rect_eq /phylog_conv /= ptr_of_phyK.
    + Ent_R_subst_con_distr.
      do 2 Ent_R_subst_apply.
      by Ent_monotony0.

(** _it <-memset( __it, [ 0 ]sc, [ 32 ]uc);; *)

idtac "43) memset".

pose init_id0 := [id ]c |---> nseq 32 pv0.
Hoare_seq_replace1 init_id init_id0.
  Hoare_frame (Hit :: init_id :: nil) (Hit :: init_id0 :: nil).
    by rewrite memset_input_inde.
  unfold init_id, init_id0.
  apply hoare_stren with (Hit ** __it |---> map phy_of_ui8 ID).
    unfold Hit at 1.
    Ent_R_rewrite_eq_p 0 (* it *).
    Ent_R_subst_con_distr.
    do 2 Ent_R_subst_apply.
    by Ent_monotony0.
  apply hoare_weak with (Hit ** __it |---> nseq 32 pv0).
    unfold Hit at 1.
    rewrite [nseq]lock.
    Ent_LR_rewrite_eq_p 0 (* it *).
    rewrite -lock.
    Ent_L_subst_apply.
    Ent_R_subst_con_distr.
    do 2 Ent_R_subst_apply.
    by Ent_monotony0.
  rewrite (_ : 32%Z = Z.of_nat 32) // (_ : [ 0 ]s = (phyint) (@pv0 _ (g.-ityp:uchar))); last first.
    apply mkPhy_irrelevance => /=.
    by rewrite zext_Z2u // Z2s_Z2u_k.

  Hoare_frame_remove (Hit :: nil); first by rewrite memset_input_inde.
  (* TODO: Hoare_frame_move seems to do a useless simpl *)
  apply memset_triple_cst_e.
  by rewrite size_map.

(** _ssl_session_0_length <-* __ssl_session_0 &-> _length; *)

idtac "44) lookup".

pose Hssl_session_0_length := `! \b __ssl_session_0_length \= (int) ([ BU2 `_ 51 ]pc : exp _ (ityp: uchar)).
Hoare_seq_ext Hssl_session_0_length.
  Hoare_L_dup (Hssl_session_0 :: nil).
  Hoare_frame (Hses_length :: Hssl_session_0 :: nil) (Hses_length :: Hssl_session_0_length :: nil).
  apply (hoare_lookup_fldp_subst _ _ssl_session_0 erefl ([ ses ]c)).
  - Ent_decompose (0 :: nil) (1 :: nil); by [apply ent_R_T | apply ent_id].
  - rewrite /=.
    Hoare_L_contract_bbang Hssl_session_0.
    apply hoare_lookup_fldp_stren.
    unfold Hses_length, mk_ssl_session.
    set ses_hdr := mk_ssl_sess_logs _ _ _.
    apply ent_R_lookup_fldp_trans with (pv := [zext 24 (BU2 `_ 51)]p) (lvs := ses_hdr).
    + by apply ent_R_con_T.
    + by rewrite /= -Eqdep.Eq_rect_eq.eq_rect_eq /phylog_conv /=.
    + Ent_R_subst_con_distr.
      do 2 Ent_R_subst_apply.
      rewrite -/Hses_length.
      Ent_monotony.
      Bbang2sbang.
      Ent_R_sbang 0; last by [].
      Rewrite_ground_bexp @sequiv_intsa_uchar_sc.
      Rewrite_ground_bexp @phy_of_si32_zext.
      Rewrite_ground_bexp @beq_exx.
      rewrite -(ground_bexp_sem (store0 sigma)).
      by apply: one_uc.

(** _it <-* __ssl_session_0 &-> _id; *)

idtac "45) lookup".

Hoare_L_contract_bbang Hit; clear Hit.

pose Hit := `! \b __it \= [ id ]c.
Hoare_seq_ext Hit.
  Hoare_L_dup (Hssl_session_0 :: nil).
  Hoare_frame (Hses_length :: Hssl_session_0 :: nil) (Hses_length :: Hit :: nil).
  apply (hoare_lookup_fldp_subst _ _ssl_session_0 Logic.eq_refl ([ ses ]c)).
  - Ent_decompose (0 :: nil) (1 :: nil); by [ | apply ent_id].
  - rewrite /=.
    Hoare_L_contract_bbang Hssl_session_0.
    apply hoare_lookup_fldp_stren.
    unfold Hses_length, mk_ssl_session.
    set ses_hdr := mk_ssl_sess_logs _ _ _.
    apply ent_R_lookup_fldp_trans with (pv := id) (lvs := ses_hdr).
    - by apply ent_R_con_T.
    - by rewrite /= -Eqdep.Eq_rect_eq.eq_rect_eq /phylog_conv /= ptr_of_phyK.
    - Ent_R_subst_con_distr.
      do 2 Ent_R_subst_apply.
      rewrite -/Hses_length.
      by Ent_monotony0.

(** memcpy _it Logic.eq_refl __it (__buf \+ [ 39 ]sc) (UINT) __ssl_session_0_length; *)

idtac "46) memcpy".

Hoare_stren_pull_out (Hsess_len ** Hsess_len_2) (u2Z (BU2 `_ 51) <= 32)%Z.
  unfold Hsess_len, Hsess_len_2.
  Ent_LR_rewrite_eq_e 0 (* sess_len *).
  do 2 Ent_LR_subst_apply.
  rewrite <- bbang_bneg_or.
  rewrite -CleqNgt.
  Ent_L_contract_bbang 0.
  Bbang2sbang.
  Ent_L_sbang 0 => H1.
  Ent_R_sbang 0; last by [].
  rewrite -(ground_bexp_sem (@store0 _ sigma)) in H1.
  apply bop_re_le_Zle in H1.
  rewrite 2!(ground_exp_sem (@store0 _ sigma)) in H1.
  by rewrite s2Z_ge_s_cst_e // s2Z_si32_of_phy_safe_cast eval_pv phy_of_ui8K in H1.
move=> BU_51.

have BU1_51 : u2nat (BU2 `_ 51) <= 32.
  rewrite [X in _ <= X](_ : 32 = '| 32 |) //; apply/leP; apply Zabs_nat_le.
  by split => //; first by apply min_u2Z.

Hoare_seq_replace1 init_id0 final_id.

  unfold Hbu.
  rewrite -(cat_take_drop 52%nat BU2) map_cat.
  Rewrite_Precond @mapstos_fit_cat.
    reflexivity.
    by rewrite -map_cat cat_take_drop size_map sz_BU2 sz_BU1 inj_mult sz_BU sizeof_ityp Z_of_nat_Zabs_nat.
  Rewrite_Postcond @mapstos_fit_con.
    reflexivity.
    by rewrite -map_cat cat_take_drop size_map sz_BU2 sz_BU1 inj_mult sz_BU sizeof_ityp Z_of_nat_Zabs_nat.
  set Hbu1 := [ bu ]c |---> _.
  rewrite size_map size_take sz_BU2 sz_BU1 sz_BU /= -(cat_take_drop (u2nat (BU2 `_ 51)) (drop 52 BU2)) map_cat.
  Rewrite_Precond @mapstos_fit_cat.
    reflexivity.
    rewrite -map_cat cat_take_drop size_map size_drop sz_BU2 sz_BU1 sz_BU sizeof_ityp; by vm_compute.  rewrite size_map size_take size_drop sz_BU2 sz_BU1 sz_BU.
  have Htmp : u2nat (BU2 `_ 51) < Z.abs_nat SSL_BUFFER_LEN - 52 by apply leq_ltn_trans with 32.
  rewrite Htmp.
  Rewrite_Postcond @mapstos_fit_con.
    reflexivity.
    rewrite -map_cat cat_take_drop size_map size_drop sz_BU2 sz_BU1 sz_BU sizeof_ityp; by vm_compute.
  rewrite size_map size_take size_drop sz_BU2 sz_BU1 sz_BU Htmp.
  set Hbu2 := [ bu ]c \+ _ |---> _.
  set Hbu3 := [ bu ]c \+ _ \+ _ |---> _.
  rewrite /init_id0 -(cat_take_drop (u2nat (BU2 `_ 51)) (nseq 32 pv0)).
  Rewrite_Precond @mapstos_fit_cat.
    reflexivity.
    rewrite cat_take_drop size_nseq sizeof_ityp; by vm_compute.
  rewrite size_take (_ : (if _ then _ else _) = u2nat (BU2 `_ 51)); last first.
     case: ifP => //.
     move/negbT.
     rewrite -leqNgt => H.
     apply/eqP.
     by rewrite eqn_leq H /= [in X in _ <= X](_ : 32 = Z.abs_nat 32).
  have sess_len_SI : sess_len SI = nat<=u (BU2 `_ 51).
    rewrite /sess_len (_ : sid = 43) // (_ : SI `_ 43 = BU2 `_ 51) // /nth' (nth_slices _ _ _ (esym BU2SI)) //=.
    - apply (@leq_trans (5 + Z.abs_nat 45)) => //.
      rewrite leq_add2l.
      apply/leP.
      by apply Zabs_nat_le.
    - rewrite leqnn andbC /=.
      apply (@leq_trans (Z.abs_nat 45)) => //.
      by apply/leP/Zabs_nat_le.
  have -> : drop (u2nat (BU2 `_ 51)) (nseq 32 pv0) = nseq (32 - sess_len SI) pv0.
    move=> ? ?; by rewrite drop_nseq // sess_len_SI.
  set init_id1 := [ id ]c |---> _.
  rewrite {1}/u2nat Z_of_nat_Zabs_nat; last by apply min_u2Z.
  set init_id2 := [ id ]c \+ [ u2Z _ ]sc |---> _.
  rewrite /final_rb /Final_rb /final_id /Final_id /sess_len_SI.
  have SI_BU : SI |{ sid.+1, u2nat (BU2 `_ 51) ) = take (u2nat (BU2 `_ 51)) (drop 52 BU2).
    rewrite (_: take (u2nat (BU2 `_ 51)) (drop 52 BU2) = BU2 |{ 52, (u2nat (BU2 `_ 51)))); last by [].
    rewrite (_: sid.+1 = 44); last by [].
    rewrite {1}(_: 44 = 5 + 39) // {1}(_: 52 = (8 + 5) + 39) //.
    eapply slice_shift.
    - symmetry; by apply BU2SI.
    - apply/ltP; apply Nat2Z.inj_lt.
      rewrite inj_plus Z_of_nat_Zabs_nat; last by omega.
      rewrite /u2nat Z_of_nat_Zabs_nat; last by apply min_u2Z.
      rewrite (_ : Z<=nat csuites.+1 = 45%Z) // /the_n_plus5 in Hsess_len_3'.
      rewrite (_ : Z<=nat 39 = 39%Z) //; omega.
  have size_slice_51 : size (SI |{ sid.+1, u2nat (BU2 `_ 51))) = u2nat (BU2 `_ 51).
    rewrite SI_BU size_take size_drop (_ : u2nat (BU2 `_ 51) < size BU2 - 52) //.
    apply leq_trans with (Z.abs_nat SSL_BUFFER_LEN - 52) => //; by rewrite sz_BU2 sz_BU1 sz_BU.
  Rewrite_Postcond @mapstos_fit_con.
    reflexivity.
    by rewrite size_cat 1!size_map size_nseq sizeof_ityp sess_len_SI size_slice_51 subnKC.
  rewrite size_map sess_len_SI size_slice_51 SI_BU Z_of_nat_Zabs_nat; last by apply min_u2Z.
  set final_id1 := [ id ]c |---> _.
  rewrite -sess_len_SI.
  set final_id2 := [ id ]c \+ [ u2Z (BU2 `_ 51) ]sc |---> _.
  Hoare_frame (Hssl_session_0_length::Hbuf :: Hit :: Hbu2 :: init_id1 :: nil)
             (Hssl_session_0_length::Hbuf :: Hit :: Hbu2 :: final_id1 :: nil).
    by rewrite memcpy_input_inde.
  rewrite /Hit /Hbuf /Hbu2 /init_id1 /final_id1.
  apply hoare_stren with (`! \b __buf \= [ bu ]c \+ [ 13 ]sc **
   `! \b __it \= [ id ]c **
   Hssl_session_0_length **
   `! \b (UINT) __ssl_session_0_length \= [ zext 24 (BU2 `_ 51) ]pc **
   __buf \+ [ 39 ]sc |---> map phy_of_ui8 (take (u2nat (BU2 `_ 51)) (drop 52 BU2)) **
   __it |---> take (u2nat (BU2 `_ 51)) (nseq 32 pv0)).
    clear.
    unfold Hssl_session_0_length.
    set tmp := nseq 32 pv0.
    rewrite [tmp]lock.
    (* TODO: nseq gets simplified, need to remove simpl from Ent_R_rewrite_bbang_re *)
    Ent_R_rewrite_eq_e 0 (*ssl_session_0_length*).
    Ent_R_subst_con_distr.
    do 6 Ent_LR_subst_apply.
    Ent_R_rewrite_eq_p 0 (* buf *).
    Ent_R_subst_con_distr.
    do 6 Ent_LR_subst_apply.
    Ent_R_rewrite_eq_p 0 (* it *).
    Ent_R_subst_con_distr.
    do 6 Ent_LR_subst_apply.
    rewrite unsa_sa_i8_to_uchar_uint_to_phy.
    do 2 rewrite -> beq_pxx.
    do 2 rewrite -> beq_exx.
    rewrite /= CaddnpA; last 3 first.
      by rewrite sizeof_ityp.
      by rewrite sizeof_ityp.
      by rewrite sizeof_ityp.
    rewrite sequiv_add_e_sc //.
    Ent_decompose (0 :: nil) (4 :: nil); first by apply ent_id.
    rewrite bbang1 !coneP; by apply ent_id.

  apply hoare_weak with (`! \b __buf \= [ bu ]c \+ [ 13 ]sc **
    `! \b __it \= [ id ]c ** Hssl_session_0_length **
    `! \b (UINT) __ssl_session_0_length \= [ zext 24 (BU2 `_ 51) ]pc **
    __buf \+ [ 39 ]sc |---> map phy_of_ui8 (take (u2nat (BU2 `_ 51)) (drop 52 BU2)) **
    __it |---> map phy_of_ui8 (take (u2nat (BU2 `_ 51)) (drop 52 BU2))).
    clear.
    unfold Hssl_session_0_length at 1.
    Ent_LR_rewrite_eq_p 0 (* buf *).
    Ent_R_subst_con_distr.
    do 5 Ent_L_subst_apply.
    do 5 Ent_R_subst_apply.
    Ent_LR_rewrite_eq_p 0 (* it *).
    Ent_R_subst_con_distr.
    do 9 Ent_LR_subst_apply.
    Ent_decompose (3 :: nil) (4 :: nil); first by apply ent_id.
    rewrite CaddnpA; last 3 first.
      by rewrite sizeof_ityp.
      by rewrite sizeof_ityp.
      by rewrite sizeof_ityp.
    rewrite sequiv_add_e_sc //.
    Ent_decompose (0 :: nil) (0 :: nil); first by apply ent_id.
    Ent_L_contract_bbang 0.
    do 2 rewrite -> beq_pxx.
    rewrite bbang1.
    by Ent_monotony.
  set tmp := nseq 32 pv0.
  rewrite [tmp]lock.
  Hoare_frame_idx_tmp (3 :: 4 :: 5 :: nil) (3 :: 4 :: 5 :: nil); first by rewrite memcpy_input_inde.
  apply memcpy_triple => //.
  - rewrite size_map size_take (_ : _ < _); last by rewrite size_drop sz_BU2 sz_BU1 sz_BU.
    rewrite Z_of_nat_Zabs_nat; last exact: min_u2Z.
    by rewrite (u2Z_zext 24).
  - rewrite size_take -lock /= /u2nat (u2Z_zext 24).
    case: ifP => //.
    rewrite Z_of_nat_Zabs_nat //; last exact: min_u2Z.
    move/negbT.
    rewrite -leqNgt => H.
    suff K : '| (Z<=u BU2 `_ 51) | = 32.
      rewrite -[in X in X = _]K Z_of_nat_Zabs_nat //; exact: min_u2Z.
    apply/eqP.
    by rewrite eqn_leq H BU1_51.

(** _buf39_plus_sess_len <-* __buf \+ ([ 39 ]sc \+ __sess_len); *)

idtac "47) lookup".

(* ciphen len part 1 *)

pose Shigh := [ BU2 `_ (52 + nat<=u (BU2 `_ 51)) ]pc : exp sigma (g.-ityp: uchar).

pose Hbuf39_plus_sess_len := `! \b __buf39_plus_sess_len \= Shigh.
Hoare_seq_ext Hbuf39_plus_sess_len.
  Hoare_frame (Hbu :: Hbuf :: Hsess_len :: nil)
             (Hbu :: Hbuf :: Hsess_len :: Hbuf39_plus_sess_len :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 52 + nat<=u (BU2 `_ 51)) (l := map phy_of_ui8 BU2) (e := [ bu ]c).
  - by rewrite size_map sizeof_ityp sz_BU2 sz_BU1 inj_mult sz_BU.
  - apply ent_R_lookup_mapstos_fit_trans.
    + rewrite size_map sz_BU2 sz_BU1 sz_BU //.
      apply leq_ltn_trans with (52 + 32); last by [].
      by rewrite leq_add2l BU1_51.
    + clear -BU_51.
      unfold Hbu.
      Ent_decompose (0 :: nil) (1 :: nil); first exact: ent_id.
      unfold Hbuf, Hsess_len.
      Ent_R_rewrite_eq_p 0 (* buf *).
      Ent_R_subst_con_distr.
      do 2 Ent_LR_subst_apply.
      Ent_LR_rewrite_eq_e 0 (* sess_len *).
      Ent_R_subst_con_distr.
      do 2 Ent_LR_subst_apply.
      rewrite sequiv_intsa_uchar_sc sequiv_add_e_sc_pos //; last 2 first.
        exact: min_u2Z.
        apply (@leZ_ltZ_trans (39 + 32)%Z) => //; omega.
      rewrite CaddnpA; last 3 first.
        by rewrite sizeof_ityp.
        rewrite sizeof_ityp mul1Z.
        move: (min_u2Z (BU2 `_ 51)) => ?; simpl expZ; omega.
        rewrite sizeof_ityp !mul1Z addZA.
        move: (min_u2Z (BU2 `_ 51)) => ?; simpl expZ; omega.
      rewrite sequiv_add_e_sc_pos //; last 2 first.
        move: (min_u2Z (BU2 `_ 51)) => ?; omega.
        apply (@leZ_ltZ_trans (13 + (39 + 32))) => //; omega.
      rewrite (_ : 13 + _ = Z.of_nat (52 + '| (u2Z (BU2 `_ 51)) |))%Z; last first.
         rewrite inj_plus Zabs2Nat.id_abs Z.abs_eq; [ring | exact: min_u2Z].
      rewrite beq_pxx bbang1; exact: ent_R_con_T.
    + rewrite addnC.
      Ent_R_subst_con_distr.
      unfold Hbu, Hbuf, Hsess_len, Hbuf39_plus_sess_len.
      do 4 Ent_LR_subst_apply.
      do 2 apply monotony_L.
      Ent_decompose (0 :: nil) (0 :: nil); first exact: ent_id.
      rewrite (nth_map zero8); last first.
        rewrite sz_BU2 sz_BU1 sz_BU.
        apply leq_ltn_trans with (Z.abs_nat 32 + 52) => //.
        rewrite leq_add2r.
        apply/leP/Zabs2Nat.inj_le => //; exact: min_u2Z.
      by rewrite addnC beq_exx bbang1.

(** _buf40_plus_sess_len <-* __buf \+ ([ 40 ]sc \+ __sess_len); *)

idtac "48) lookup".

pose Slow : @exp g sigma (g.-typ: ityp uchar) := [ BU2 `_ (53 + nat<=u (BU2 `_ 51)) ]pc.

pose Hbuf40_plus_sess_len := `! \b __buf40_plus_sess_len \= Slow.
Hoare_seq_ext Hbuf40_plus_sess_len.
  Hoare_frame (Hbu :: Hbuf :: Hsess_len :: nil)
             (Hbu :: Hbuf :: Hsess_len :: Hbuf40_plus_sess_len :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 53 + Z.abs_nat (u2Z (BU2 `_ 51))) (l := map phy_of_ui8 BU2) (e := [ bu ]c).
  - rewrite size_map sizeof_ityp sz_BU2 sz_BU1 inj_mult sz_BU; by vm_compute.
  - apply ent_R_lookup_mapstos_fit_trans.
    + rewrite size_map sz_BU2 sz_BU1 sz_BU //.
      apply leq_ltn_trans with (53 + 32); last by [].
      by rewrite leq_add2l.
    + unfold Hbu.
      Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
      unfold Hbuf, Hsess_len, Hsess_len_2.
      Ent_R_rewrite_eq_p 0 (* buf *).
      Ent_R_subst_con_distr.
      do 2 Ent_LR_subst_apply.
      Ent_LR_rewrite_eq_e 0 (* sess_len *).
      Ent_R_subst_con_distr.
      do 2 Ent_LR_subst_apply.
      rewrite sequiv_intsa_uchar_sc sequiv_add_e_sc_pos //; last 2 first.
        by apply min_u2Z.
        apply (@leZ_ltZ_trans (40 + 32)%Z) => //; omega.
      rewrite CaddnpA; last 3 first.
        by rewrite sizeof_ityp.
        clear -BU_51.
        rewrite sizeof_ityp mul1Z.
        move: (min_u2Z (BU2`_51)) => ?; simpl expZ; omega.
        rewrite sizeof_ityp !mul1Z addZA.
        move: (min_u2Z (BU2`_51)) => ?; simpl expZ; omega.
      rewrite sequiv_add_e_sc_pos //; last 2 first.
        clear -BU_51.
        move: (min_u2Z (BU2 `_ 51)) => ?; omega.
        clear -BU_51.
        apply (@leZ_ltZ_trans (13 + (40 + 32))) => //; omega.
      rewrite (_ : 13 + _ = Z.of_nat (53 + Z.abs_nat (u2Z (BU2 `_ 51))))%Z; last first.
         rewrite inj_plus Zabs2Nat.id_abs Z.abs_eq; [ring | exact: min_u2Z].
      rewrite beq_pxx bbang1; exact: ent_R_con_T.
    + rewrite addnC.
      Ent_R_subst_con_distr.
      unfold Hbu, Hbuf, Hsess_len, Hbuf39_plus_sess_len.
      do 4 Ent_LR_subst_apply.
      Ent_decompose (0 :: 1 :: 2 :: nil) (0 :: 1 :: 2 :: nil); first by apply ent_id.
      rewrite (nth_map zero8); last first.
        rewrite sz_BU2 sz_BU1 sz_BU.
        apply leq_ltn_trans with (Z.abs_nat 32 + 53) => //.
        rewrite leq_add2r.
        apply/leP/Zabs2Nat.inj_le => //; exact: min_u2Z.
      by rewrite addnC beq_exx bbang1.

(** _ciph_len <- (int) __buf39_plus_sess_len \<\< [ 8 ]sc \| (int) __buf40_plus_sess_len; *)

idtac "49) assign".

pose Hciph_len := `! \b __ciph_len \= ((int) Shigh \<< [ 8 ]sc \| (int) Slow).
Hoare_seq_ext Hciph_len.
  Hoare_L_dup (Hbuf39_plus_sess_len :: Hbuf40_plus_sess_len :: nil).
  unfold final_id, Final_id, final_rb, Final_rb.
  Hoare_frame (Hbuf39_plus_sess_len :: Hbuf40_plus_sess_len :: nil) (Hciph_len :: nil).
  apply hoare_assign_stren.
  Ent_LR_subst_apply.
  unfold Hbuf39_plus_sess_len.
  Ent_LR_rewrite_eq_e 0. (* buf39+sess_len *)
  do 2 Ent_LR_subst_apply.
  Ent_LR_rewrite_eq_e 0. (* buf40+sess_len*)
  Ent_LR_subst_apply.
  by Ent_monotony0.

Hoare_L_contract_bbang Hbuf39_plus_sess_len.
Hoare_L_contract_bbang Hbuf40_plus_sess_len.
clear Hbuf39_plus_sess_len Hbuf40_plus_sess_len.

(**  If  \b __ciph_len \< [ 2 ]sc \|| __ciph_len \> [ 256 ]sc \||
          __ciph_len \% 1 \!= [ 0 ]sc \||
          [ Z<=nat 46 ]sc \+ __sess_len \+ __ciph_len \>= [ 5 ]sc \+ __n_old  Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "50) ifte".

apply hoare_ifte_bang; first by apply POLAR_ret_err.
rewrite -bbang_bneg_or.
set Hciph_len_bound := `! \~b \b __ciph_len \< [ 2 ]sc \|| __ciph_len \> [ 256 ]sc \|| __ciph_len \% 1 \!= [ 0 ]sc.
set Hciph_len_bound2 := `! \~b \b [Z<=nat compmeth ]sc \+ __sess_len \+ __ciph_len \>= [ 5 ]sc \+ __n_old.
pose ciph_len_exp : exp sigma _ := (int) Shigh \<< [ 8 ]sc \| (int) Slow.
pose ciph_len_value := @ground_exp g sigma _ ciph_len_exp erefl.
pose ciph_len_value_Z := s2Z (si32<=phy ciph_len_value).
pose ciph_len_value_nat := '| ciph_len_value_Z |.
Hoare_stren_pull_out (Hciph_len ** Hciph_len_bound) (2 <= ciph_len_value_Z <= 256)%Z.
  rewrite /Hciph_len /Hciph_len_bound. rewrite -/ciph_len_exp.
  rewrite <- bbang_bneg_or.
  rewrite <- bbang_bneg_or.
  rewrite -CleqNgt -CgeqNlt.
  Ent_LR_rewrite_eq_e 0 (* ciph_len *).
  do 4 Ent_LR_subst_apply.
  Ent_L_contract_bbang 2.
  Bbang2sbang.
  Ent_L_sbang 0 => H1.
  Ent_L_sbang 0 => H2.
  Ent_R_sbang 0; last by [].
  rewrite -(ground_bexp_sem (@store0 _ sigma))in H1; apply bop_re_ge_Zge in H1.
  rewrite -(ground_bexp_sem (@store0 _ sigma))in H2; apply bop_re_le_Zle in H2.
  rewrite 2!(ground_exp_sem (@store0 _ sigma)) -/ciph_len_value -/ciph_len_value_Z s2Z_ge_s_cst_e // in H1.
  rewrite 2!(ground_exp_sem (@store0 _ sigma)) -/ciph_len_value -/ciph_len_value_Z s2Z_ge_s_cst_e // in H2.
  omega.
move => Hciph_len_bound_Z.

have Hciph_len_bound_nat : 2 <= ciph_len_value_nat <= 256.
  rewrite [X in _ <= _ <= X](_ : 256%nat = Z.abs_nat 256) // [X in X < _ <= _](_ : 1%nat = Z.abs_nat 1) //.
  apply/andP; split.
    apply/ltP/Zabs_nat_lt; omega.
  apply/leP/Zabs_nat_le; omega.

pose Hciph_len_bound2'' := !!(Z<=nat compmeth + Z<=u BU2 `_ 51 + ciph_len_value_Z < the_n_plus5)%Z.
Hoare_L_stren_by Hciph_len_bound2'' (Hsess_len :: Hn_old :: Hciph_len :: Hciph_len_bound2 :: nil).
  unfold Hn_old, Hsess_len, Hciph_len, Hciph_len_bound2.
  Ent_LR_rewrite_eq_e 0 (* ciph_len *).
  do 4 Ent_LR_subst_apply.
  fold Hciph_len_bound2''.
  Ent_LR_rewrite_eq_e 0 (* sess_len *).
  do 3 Ent_LR_subst_apply.
  fold Hciph_len_bound2''.
  Ent_LR_rewrite_eq_e 0 (* n old *).
  do 2 Ent_LR_subst_apply.
  rewrite -/Shigh -/Slow -/ciph_len_exp.
  Bbang2sbang.
  apply ent_sbang_sbang.
  rewrite gb_bneg_bop_r_ge.
  move/Zlt_gb. move/(_ erefl erefl).
  rewrite si32_of_phy_gb_add_e si32_of_phy_gb_add_e si32_of_phy_gb_add_e ge_cast_sint_cst_8c.
  rewrite (phy_of_si32K (zext 24 BU2 `_ 51)) 3!i32_ge_s_cst_e -/ciph_len_value.
  have H1 : (0 <= Z<=nat compmeth + Z<=u BU2 `_ 51 + ciph_len_value_Z < 2 ^^ 31)%Z.
    split.
      apply (@leZ_trans (Z0 + Z0 + 2)) => //.
      apply leZ_add => //.
      apply leZ_add => //; exact: min_u2Z.
    by case: Hciph_len_bound_Z.
    apply (@leZ_ltZ_trans (Z<=nat compmeth + 2 ^^ 8 + 256)) => //.
    apply leZ_add.
      exact/leZ_add2l/ltZW/max_u2Z.
    by case: Hciph_len_bound_Z.
  have -> : (Z<=s ((Z2s 32 (Z<=nat compmeth) `+ zext 24 BU2 `_ 51) `+
        si32<=phy ciph_len_value) = Z<=nat compmeth + u2Z (BU2 `_ 51) + ciph_len_value_Z)%Z.
    rewrite s2Z_add; last first.
      rewrite s2Z_add; last first.
        rewrite Z2sK // (s2Z_zext 24) //.
        move: (min_u2Z BU2 `_ 51) => ?; omega.
      rewrite Z2sK // (s2Z_zext 24) // -/ciph_len_value_Z; omega.
    rewrite s2Z_add; last first.
      rewrite Z2sK // (s2Z_zext 24) //.
      move: (min_u2Z BU2 `_ 51) => ?; omega.
    by rewrite Z2sK // (s2Z_zext 24).
  rewrite s2Z_add; last first.
    rewrite Z2sK // Z2sK; last by simpl expZ; omega.
    simpl expZ; omega.
  rewrite Z2sK // Z2sK; last by simpl expZ; omega.
  apply.
  exact H1.
  simpl expZ; omega.

apply hoare_pullout_sbang => Hciph_len_bound2'.
clear Hciph_len_bound2''.
Hoare_L_contract_bbang Hciph_len_bound2; clear Hciph_len_bound2.

(** _comp_len' <-* __buf \+ ([ 41 ]sc \+ __sess_len \+ __ciph_len); *)

idtac "51) lookup".

pose comp_len'_exp : exp sigma (ityp: uchar) := [ BU2 `_ (54 + u2nat (BU2 `_ 51) + ciph_len_value_nat) ]pc.
pose comp_len'_value := @ground_exp g sigma _ comp_len'_exp erefl.
pose comp_len'_value_nat := nat<=u (i8<=phy comp_len'_value).
pose Hcomp_len' := `! \b __comp_len' \= [comp_len'_value]c.
Hoare_seq_ext Hcomp_len'.
  Hoare_L_dup (Hsess_len :: Hsess_len_2 :: Hciph_len :: Hciph_len_bound::nil).
  unfold final_id, Final_id, final_rb, Final_rb.
  Hoare_frame (Hbu :: Hbuf :: Hsess_len :: Hsess_len_2 :: Hciph_len :: Hciph_len_bound :: nil)
    (Hbu :: Hbuf :: Hcomp_len' :: nil).
  apply hoare_lookup_mapstos_fit_stren with (i := 54 + u2nat (BU2 `_ 51) + ciph_len_value_nat) (l := map phy_of_ui8 BU2) (e := [ bu ]c).
  - rewrite size_map sizeof_ityp sz_BU2 sz_BU1 inj_mult sz_BU; by vm_compute.
  - apply ent_R_lookup_mapstos_fit_trans.
    + rewrite size_map sz_BU2 sz_BU1 sz_BU // /SSL_BUFFER_LEN -(_: '| 54 | = 54%nat) // /ciph_len_value_nat.
      move: (min_u2Z (BU2 `_ 51)) => ?.
      rewrite -!plusE -Zabs_nat_Zplus // -Zabs_nat_Zplus; last 2 first.
        apply addZ_ge0 => //; exact: min_u2Z.
        case: Hciph_len_bound_Z => Htmp _; by apply: leZ_trans; last by apply Htmp.
      apply/ltP; apply Zabs2Nat.inj_lt; omega.
    + unfold Hbu.
      Ent_decompose (0 :: nil) (1 :: nil); first by apply ent_id.
      rewrite /Hbuf /Hsess_len /Hciph_len /Hsess_len_2 /Hciph_len_bound -/ciph_len_exp.
      Ent_L_contract_bbang 2.
      Ent_L_contract_bbang 3.
      Ent_LR_rewrite_eq_p 0 (* buf *).
      do 2 Ent_LR_subst_apply.
      Ent_R_subst_con_distr.
      do 2 Ent_LR_subst_apply.
      Ent_LR_rewrite_eq_e 0 (* sess_len *).
      Ent_LR_subst_apply.
      Ent_R_subst_con_distr.
      do 2 Ent_LR_subst_apply.
      rewrite -/Slow -/Shigh -/ciph_len_exp.
      Ent_LR_rewrite_eq_e 0 (* ciph_len *).
      Ent_R_subst_con_distr.
      do 2 Ent_LR_subst_apply.
      Bbang2sbang.
      Ent_R_sbang 0; last by [].
      rewrite -(ground_bexp_sem (store0 sigma)).
      rewrite beval_eq_p_eq.
      clear -BU_51 Hciph_len_bound_Z.
      move: (min_u2Z (BU2 `_ 51)) => ?.
      have Hoverflow:
        (s2Z (si32<=phy (ground_exp ([ 41 ]sc \+ (int) ([ BU2 `_ 51 ]pc : exp sigma (ityp: uchar)) \+ ciph_len_exp) erefl)) =
         41 + u2Z (BU2 `_ 51) + s2Z (si32<=phy (ground_exp ciph_len_exp erefl)))%Z.
        rewrite 2!si32_of_phy_gb_add_e (@i32_ge_s_cst_e g sigma) ge_cast_sint_cst_8c.
        rewrite phy_of_si32K 2!s2Z_add Z2sK // (s2Z_zext 24) // -/ciph_len_value_Z; simpl expZ; omega.
      case: Hciph_len_bound_Z => H H0.
      rewrite eval_add_pA; first last.
      - rewrite Hoverflow sizeof_ityp [sizeof_integral _]/= 2!mul1Z si32_of_phy_sc Z2sK // -/ciph_len_value_Z.
        simpl expZ; omega.
      - rewrite Hoverflow sizeof_ityp [sizeof_integral _]/= mul1Z -/ciph_len_value_Z.
        simpl expZ; omega.
      - by rewrite sizeof_ityp [sizeof_integral _]/= mul1Z si32_of_phy_sc Z2sK.
      rewrite -beval_eq_p_eq.
      apply Ceqpn_add2l'.
      rewrite beval_eq_e_eq.
      apply/eqP/si32_of_phy_inj.
      rewrite 3!si32_of_phy_binop_ne 3!si32_of_phy_sc.
      apply s2Z_inj.
      rewrite (ground_exp_sem (store0 sigma)) (@ge_cast_sint_cst_8c g sigma) phy_of_si32K // Z2sK; last first.
        rewrite 2!inj_plus Z_of_nat_Zabs_nat; last by apply min_u2Z.
        rewrite (_ : Z<=nat 54 = 54%Z) // /ciph_len_value_Z Z_of_nat_Zabs_nat; simpl expZ; omega.
      rewrite s2Z_add Z2sK // s2Z_add // -/ciph_len_value_Z s2Z_add Z2sK // (s2Z_zext 24) //; try by simpl expZ; omega.
      rewrite !inj_plus Z_of_nat_Zabs_nat; last by apply min_u2Z.
      rewrite /ciph_len_value_nat (_ : Z<=nat 54 = 54%Z) // Z_of_nat_Zabs_nat; last by omega.
      ring.
  + Ent_R_subst_con_distr.
    rewrite [nth]lock.
    do 3 Ent_LR_subst_apply.
    Ent_decompose (0 :: 1 :: nil) (0 :: 1 :: nil); first by apply ent_id.
    do 4 Ent_L_contract_bbang 0.
    Bbang2sbang.
    Ent_R_sbang 0; last by [].
    rewrite -lock gb_eq_e; apply/eqP.
    rewrite /comp_len'_value /comp_len'_exp 3!ge_cst_e (nth_map (Z2u 8 0)) // sz_BU2 sz_BU1 sz_BU /SSL_BUFFER_LEN.
    apply ltn_trans with (54 + 32 + 256 + 1); last by vm_compute.
    rewrite -!addnA ltn_add2l ltn_leq_add2l // -(addn0 ciph_len_value_nat) ltn_leq_add2l //.
    by case/andP : Hciph_len_bound_nat.

(** _comp_len <- (int) __comp_len'; *)

idtac "52) assign".

pose comp_len_exp := (int) ([ BU2 `_ (54 + u2nat (BU2 `_ 51) + ciph_len_value_nat) ]pc : exp sigma (ityp: uchar)).
pose comp_len_value := @ground_exp _ sigma _ comp_len_exp erefl.
pose Hcomp_len := `! \b __comp_len \= [comp_len_value]c.
Hoare_seq_ext Hcomp_len.
  Hoare_L_dup (Hcomp_len' :: nil).
  unfold final_id, Final_id, final_rb, Final_rb.
  Hoare_frame (Hcomp_len' :: nil) (Hcomp_len :: nil).
  apply hoare_assign_stren.
  unfold Hcomp_len, Hcomp_len'.
  Ent_LR_subst_apply.
  Ent_LR_rewrite_eq_e 0 (* comp_len'*).
  Ent_LR_subst_apply.
  Bbang2sbang; Ent_R_sbang 0; last by [].
  unfold comp_len_value, comp_len'_value.
  Rewrite_ground_bexp @sequiv_ge.
  Rewrite_ground_bexp @sequiv_ge.
  Rewrite_ground_bexp @beq_exx.
  exact: oneuc.

(** IIf  \b __comp_len \< [ 1 ]sc \|| __comp_len \> [ 16 ]sc \||
          [ Z<=nat 47 ]sc \+ __sess_len \+ __ciph_len \+ __comp_len \!=
          [ 5 ]sc \+ __n_old  Then *)
(**   _ret <- [ POLARSSL_ERR_SSL_BAD_HS_CLIENT_HELLO ]c; Return *)

idtac "53) ifte".
apply hoare_ifte_bang; first by apply POLAR_ret_err.
rewrite -bbang_bneg_or.
set Hextensions := `! \~b \b [ Z<=nat compmeth.+1 ]sc \+ __sess_len \+ __ciph_len \+ __comp_len \!= [ 5 ]sc \+ __n_old.

Hoare_L_contract_bbang Hcomp_len'.
clear Hcomp_len' comp_len'_value comp_len'_exp comp_len'_value_nat.

(** "_goto_have_cipher_" <- [ 0 ]sc; *)

idtac "54) assign".

pose H_goto_have_cipher := `! \b __goto_have_cipher \= [ 0 ]sc.
Hoare_seq_ext H_goto_have_cipher.
  Hoare_frame (@nil assert) (H_goto_have_cipher :: nil).
  apply hoare_assign_stren.
  Ent_LR_subst_apply.
  Bbang2sbang.
  Ent_R_sbang 0; last by [].
  Rewrite_ground_bexp @sequiv_bop_re_sc => //=.
  exact: oneuc.

Require Import POLAR_parse_client_hello_triple3.

idtac "before apply POLAR_parse_client_hello_triple3".

by apply POLAR_parse_client_hello_triple3 with (BU := BU) (in_left0 := in_left) (BU1 := BU1).
Qed.

End POLAR_parse_client_hello_triple.
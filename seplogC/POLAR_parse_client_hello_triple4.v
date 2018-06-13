(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import Div2 Even.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import tuple.
Require Import ssrZ ZArith_ext String_ext seq_ext.
Require Import seq_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_expr_equiv C_expr_ground C_seplog C_tactics.
Require Import rfc5246.
Import RFC5932.
Require Import POLAR_library_functions POLAR_library_functions_triple.
Require Import POLAR_ssl_ctxt POLAR_parse_client_hello POLAR_parse_client_hello_header.

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

(** * Verification of the ClientHello Parsing Program (4/4) *)

Section POLAR_parse_client_hello_triple.

Variable SI : seq (int 8).

Lemma POLAR_parse_client_hello_triple4 (BU RB : seq (int 8)) (CI : seq (int 32))
  (HCI : ciphers_seq CI)
  (cipher0 length0 : int 32)
  (bu rb id : (:* (ityp: uchar)).-phy)
  (ses : (:* (g .-typ: ssl_session)).-phy)
  (ciphers : (:* (ityp: sint)).-phy)
  (vssl : int ptr_len)
  (md5s sha1s : 5.-tuple (int ptr_len)) :
  let init_ssl_var := `! \b __ssl \= [ phy<=ptr _ vssl ]c in
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
  forall BU1 : seq (int 8), BU1 |{ 8, 5) = SI |{ 0, 5) -> size BU1 = size BU ->
  forall in_left0, in_left0 = `( 5 )_32 ->
  let the_n := Z<=s ((zext 24 BU1 `_ 11 `<< 8) `|` zext 24 BU1 `_ 12) in
  let the_n_plus5 := (5 + the_n)%Z in
  (45 <= the_n)%Z -> (the_n <= 512)%Z ->
  forall in_left2, in_left2 = `( the_n_plus5 )_32 ->
  forall BU2 : seq (int 8),
  let Hbu := [ bu ]c |---> map phy<=ui8 BU2 in
  BU2 |{ 8 + 5, '| the_n |) = SI |{ 5, '| the_n |) ->
  BU2 |{ 8, 5) = BU1 |{ 8, 5) ->
  size BU2 = size BU1 ->
  '| the_n_plus5 | <= size SI ->
  let Hbuf := `! \b __buf \= [ bu ]c \+ [ 13 ]sc in
  let Hn0 := `! \b __n0 \= [ in_left2 ]pc in
  let Hn_old := `! \b __n_old \= [ the_n ]sc in
  let Hn := `! \b __n \= __n0 \- [ 5 ]sc in
  BU1 `_ 8 `& `( 128 )_8 = `( 0 )_8 /\ BU1 `_ 8 = S621.handshake ->
  BU2 `_ 13 = S74.client_hello ->
  BU2 `_ 17 = S621.SSLv30_maj ->
  let Hbuf5 := `! \b __buf5 \= [ BU2 `_ 18 ]pc in
  let minver_exp : exp sigma _ :=
    [ BU2 `_ 18 ]pc \<= [ SSL_MINOR_VERSION_2 ]c \?
    [ BU2 `_ 18 ]pc \: [ SSL_MINOR_VERSION_2 ]c in
  let minver_u := si32<=phy ((phyint) (ground_exp minver_exp erefl)) in
  let reqmin_sslcontext := Ssl_context (zext 24 S74.client_hello)
             (si32<=phy ((phyint) SSL_MAJOR_VERSION_3))
             minver_u (zext 24 BU2 `_ 17) (zext 24 BU2 `_ 18)
             ses bu in_left2 md5s sha1s ciphers rb in
  BU1 `_ 9 = S621.SSLv30_maj ->
  BU2 `_ 14 = zero8 ->
  let Hm := `! \b __n \= [ 4 ]sc \+
         ((int) ([ BU2 `_ 15 ]pc : exp _ (ityp: uchar)) \<< [ 8 ]sc \|
          (int) ([ BU2 `_ 16 ]pc : exp _ (ityp: uchar))) in
  let Hsess_len := `! \b __sess_len \= (int) ([ BU2 `_ 51 ]pc : exp _ (ityp: uchar)) in
  let Hsess_len_bound := `! \~b \b __sess_len \< [ 0 ]sc \|| __sess_len \> [ 32 ]sc in
  let Hssl_session_0 := `! \b __ssl_session_0 \= [ ses ]c in
  (Z<=nat csuites.+1 + Z<=u BU2 `_ 51 < the_n_plus5)%Z ->
  let Hses_length := ses |lV~> mk_ssl_session cipher0 (zext 24 BU2 `_ 51) (ptr<=phy id) in
  let Hssl_session_0_length :=
      `! \b __ssl_session_0_length \= (int) ([ BU2 `_ 51 ]pc : exp _ (ityp: uchar)) in
  let Hit := `! \b __it \= [ id ]c in
  (Z<=u BU2 `_ 51 <= 32)%Z ->
  nat<=u BU2 `_ 51 <= 32 ->
  let Shigh : exp _ (ityp: uchar):= [ BU2 `_ (52 + nat<=u BU2 `_ 51) ]pc in
  let Slow : exp _ (ityp: uchar) := [ BU2 `_ (53 + nat<=u BU2 `_ 51) ]pc in
  let Hciph_len := `! \b __ciph_len \= ((int) Shigh \<< [ 8 ]sc \| (int) Slow) in
  let Hciph_len_bound := `! \~b
       \b __ciph_len \< [ 2 ]sc \|| __ciph_len \> [ 256 ]sc \|| __ciph_len \% 1 \!= [ 0 ]sc in
  let ciph_len_exp := (int) Shigh \<< [ 8 ]sc \| (int) Slow in
  let ciph_len_value := ground_exp ciph_len_exp erefl in
  let ciph_len_value_Z := Z<=s (si32<=phy ciph_len_value) in
  let ciph_len_value_nat := '| ciph_len_value_Z | in
  (Z<=nat compmeth + Z<=u BU2 `_ 51 + ciph_len_value_Z < the_n_plus5)%Z ->
  (2 <= ciph_len_value_Z <= 256)%Z ->
  1 < ciph_len_value_nat <= 256 ->
  let comp_len_exp : exp sigma _ := (int)
      ([ BU2 `_ (54 + nat<=u BU2 `_ 51 + ciph_len_value_nat) ]pc : exp sigma (ityp: uchar)) in
  let comp_len_value := ground_exp comp_len_exp Logic.eq_refl in
  let Hcomp_len := `! \b __comp_len \= [ comp_len_value ]c in
  let Hextensions := `! \~b
    \b [ Z<=nat (compmeth.+1) ]sc \+ __sess_len \+ __ciph_len \+ __comp_len \!=
       [ 5 ]sc \+ __n_old in
  let Hciph_len_even := sepex k', !!((Z<=nat k' * 2 < 2 ^^ 30)%Z) **
                                  `! \b __ciph_len \= [ Z<=nat k' * 2 ]sc in
  let inv_outer := reqmin_sslcontext ** Hbuf ** Hbu **
    init_ciphers ** Hciph_len ** Hciph_len_even **
    Hsess_len ** Hses_length **
    (`! \b __goto_have_cipher \= [ 1 ]sc **
     (sepex i, (!!(i < size CI)) **
      (sepex k, (!!(k < 128)) **
       `! \b [ Z<=nat k * 2 ]sc \< __ciph_len **
       `! \b __ssl_ciphers_i \= [ CI `32_ i ]pc **
       !!( BU2 `_ (54 + nat<=u (BU2 `_ 51) + 2 * k) = `( 0 )_ 8 ) **
       `! \b (int) __ssl_ciphers_i \= (int) ([ BU2 `_ (54 + nat<=u BU2 `_ 51 + k * 2 + 1) ]pc : exp _ (ityp: uchar))))) \\//
    `! \b __goto_have_cipher \= [ 0 ]sc **
    ((`! \b __ssl_ciphers_i \!= [ 0 ]sc **
     (sepex i, (!!(i < size CI)) **
      `! \b __i \= [ Z<=nat i ]sc **
      `! \b __ssl_ciphers_i \= [ CI `32_ i ]pc)) \\//
    `! \b __ssl_ciphers_i \= [ 0 ]sc) in
{{ Hcomp_len ** Hit ** Hssl_session_0_length ** Hssl_session_0 ** Hm **
   Hbuf5 ** Hn ** Hn_old ** Hn0 ** success ** init_ssl_var ** final_rb **
   final_id ** Hsess_len_bound ** Hciph_len_bound **
   `! \~b \b __comp_len \< [ 1 ]sc \|| __comp_len \> [ 16 ]sc ** Hextensions ** inv_outer }}
 ssl_parse_client_hello5
{{ error \\//
   success ** final_bu ** final_ses ** final_rb ** final_id **
   final_ssl_context ** !!(PolarSSLClientHellop SI) ** init_ciphers }}.
Proof.
move=> init_ssl_var init_ciphers final_bu final_ses final_rb
  final_id final_ssl_context BU1 BU1SI sz_BU1 in_left0 in_left0_5
  the_n the_n_plus5 HN1 HN0 in_left2 in_left2_n5 BU2 Hbu BU2SI
  BU2BU1 sz_BU2 HSI_new Hbuf Hn0 Hn_old Hn BU1_8 BU2_13 BU2_17
  Hbuf5 minver_exp minver_u reqmin_sslcontext BU1_9 BU2_14 Hm Hsess_len
  Hsess_len_bound Hssl_session_0 csuites_max Hses_length
  Hssl_session_0_length Hit BU_51 BU1_51 Shigh Slow Hciph_len
  Hciph_len_bound ciph_len_exp ciph_len_value ciph_len_value_Z
  ciph_len_value_nat compmeth_max Hciph_len_bound_Z
  Hciph_len_bound_nat comp_len_exp comp_len_value
  Hcomp_len Hextensions Hciph_len_even inv_outer.

unfold ssl_parse_client_hello5.

(** If \b __goto_have_cipher \!= [ 0 ]sc Then *)

(** Else
      _ret <- [ POLARSSL_ERR_SSL_NO_CIPHER_CHOSEN ]c; Return *)

idtac "71) ifte".

Hoare_ifte_bang Hgoto_have_cipher0; last by apply POLAR_ret_err.

(** __ssl_session_0 &-> _cipher *<- __ssl_ciphers_i; *)

idtac "72) mutation".

unfold inv_outer.
Hoare_L_or 0 (* NB: do not work with 1 *); last first.
  apply hoare_stren with FF; last by apply hoare_L_F.
  rewrite /Hgoto_have_cipher0 [in X in _ ** X ===> _]bneq_neg_eq.
  set H1 := `! \b __goto_have_cipher \= _.
  set H2 := `! \~b \b __goto_have_cipher \= _.
  by Ent_L_contradict (H1 :: H2 :: nil).
Hoare_L_ex O i.
Hoare_L_ex O k.
set ssl_cipher_i := BU2 `_ (54 + nat<=u BU2 `_ 51 + k * 2 + 1).
set Hssl_cipher_i := `! \b __ssl_ciphers_i \= [ CI `32_ i ]pc.
pose Hses_cipher := ses |lV~> mk_ssl_session (CI `32_ i) (zext 24 (BU2 `_ 51)) (ptr<=phy id).
Hoare_seq_replace1 Hses_length Hses_cipher.
  Hoare_L_dup (Hssl_cipher_i :: Hssl_session_0 :: nil).
  Hoare_frame (Hssl_cipher_i :: Hssl_session_0 :: Hses_length :: nil) (Hses_cipher :: nil).
  unfold Hses_length, Hses_cipher.
  apply hoare_mutation_fldp_subst_ityp with (str := _ssl_ciphers_i) (e := [ CI `32_ i ]pc) (Hstr := erefl).
  - by apply monotony_L.
  - rewrite /=.
    Hoare_L_contract_bbang Hssl_cipher_i.
    apply hoare_mutation_fldp_subst_ptr with (str := _ssl_session_0) (e'' := [ ses ]c) (Hstr := erefl).
    + by apply monotony_L.
    + rewrite /=.
      Hoare_L_contract_bbang Hssl_session_0.
      eapply hoare_weak; last first.
        have He2 : @vars _ sigma (ityp: sint) [ CI `32_ i ]pc = nil by done.
        apply hoare_mutation_fldp_local_forward_ground_lV with (val := mkSintLog CI `32_ i) (He2 := He2).
        by rewrite /phylog_conv /= ge_cst_e.
      rewrite /= -Eqdep.Eq_rect_eq.eq_rect_eq; by apply ent_id.

(** __ssl &-> _in_left *<- [ 0 ]sc; *)

idtac "73) mutation".

pose Hssl_in_left3 := Ssl_context (zext 24 S74.client_hello) 
  (si32<=phy ((phyint) SSL_MAJOR_VERSION_3)) minver_u (zext 24 (BU2 `_ 17)) 
  (zext 24 (BU2 `_ 18)) ses bu `( 0 )s_32 md5s sha1s ciphers rb.
Hoare_seq_replace1 reqmin_sslcontext Hssl_in_left3.
  Hoare_frame (reqmin_sslcontext :: nil) (Hssl_in_left3 :: nil).
  eapply hoare_weak; last first.
    have He2 : @vars _ sigma (ityp: sint) [ 0 ]sc = nil by done.
    apply hoare_mutation_fldp_local_forward_ground_le with (val := mkSintLog `( 0 )s_32) (He2 := He2).
    by rewrite /phylog_conv /= ge_cst_e.
  rewrite set_in_left_ssl_ctxt; by apply ent_id.

(** _ssl_state <-* __ssl &-> _state; *)

idtac "74) lookup".

pose H_ssl_state := `! \b __ssl_state \= [ Z<=u S74.client_hello ]sc.
Hoare_seq_ext H_ssl_state.
  Hoare_frame (Hssl_in_left3 :: nil) (Hssl_in_left3 :: H_ssl_state :: nil).
  apply hoare_lookup_fldp_stren.
  apply ent_R_lookup_fldp with (pv := [ u2Z S74.client_hello ]s ).
  - rewrite get_state_ssl_ctxt /phylog_conv /=.
    apply/eqP/mkPhy_irrelevance => /=.
    congr (i8<=i32).
    apply/u2Z_inj.
    by rewrite (u2Z_zext 24) 2!u2ZE Z2sE.
  - clear.
    Ent_R_subst_con_distr.
    rewrite [in X in _ ===> X ** _]wp_assign_mapsto_le.
    apply monotony_L2.
    Ent_R_subst_apply.
    by Ent_monotony0.

(** __ssl &-> _state *<- __ssl_state \+ [ 1 ]sc; *)

pose Hssl_server := Ssl_context (zext 24 S74.server_hello)
  (si32<=phy ((phyint) SSL_MAJOR_VERSION_3)) minver_u (zext 24 (BU2 `_ 17)) 
  (zext 24 (BU2 `_ 18)) ses bu `( 0 )s_32 md5s sha1s ciphers rb.
Hoare_seq_replace1 Hssl_in_left3 Hssl_server.

idtac "75) mutation".

  Hoare_L_dup (H_ssl_state :: nil).
  Hoare_frame (H_ssl_state :: Hssl_in_left3 :: nil) (Hssl_server :: nil).
  apply hoare_mutation_fldp_subst_ityp with (str := _ssl_state) (e := [ Z<=u S74.client_hello ]sc) (Hstr := erefl).
  - by apply monotony_L.
  - rewrite /=.
    Hoare_L_contract_bbang H_ssl_state.
    eapply hoare_weak; last first.
      have He2 : @vars _ sigma (ityp: uchar) [S74.server_hello]pc = nil by done.
      apply hoare_mutation_fldp_local_forward_ground_le with (val := mkSintLog (zext 24 S74.server_hello)) (He2 := He2).
      rewrite /phylog_conv /= -(ground_exp_sem (store0 sigma)) sequiv_add_e_sc_pos; last 3 first.
        by apply min_u2Z.
        by vm_compute.
        by rewrite u2ZE.
      rewrite (ground_exp_sem (store0 sigma)) ge_cst_e /=.
      apply/eqP/mkPhy_irrelevance => /=.
      congr (i8<=i32).
      apply u2Z_inj.
      by rewrite (u2Z_zext 24) 3!u2ZE Z2sE.
    rewrite set_state_ssl_ctxt /=; by apply ent_id.
apply hoare_R_or_2. (* success branch *)

(** _ret <- [ 0 ]sc; Return *)

match goal with
|- {{ ?P }} _ ; _ {{ _ }} => apply hoare_seq with P
end.
  Hoare_frame (success :: nil) (success :: nil).
  clear.
  apply hoare_assign_stren.
  Ent_R_subst_apply.
  rewrite bbang_eq_exx; by apply ent_bang_contract.

(** Return *)

unfold Return.
eapply hoare_stren; last by apply hoare_hoare0, hoare0_skip.
Ent_decompose (17 (* success *) :: nil) (0 (* success*) :: nil); first by apply ent_id.
have the_n_n_SI : '| the_n | = n SI.
  rewrite /n /n'; congr ('| _ |).
  rewrite /the_n /multi_int.bSum_c /=.
  rewrite (_ : BU1 `_ 11 = SI `_ record_sz); last by rewrite /nth' (nth_slices _ _ _ BU1SI).
  rewrite (_ : BU1 `_ 12 = SI `_ record_sz.+1); last by rewrite /nth' (nth_slices _ _ _ BU1SI).
  rewrite (_ : zext 24 (SI `_ record_sz) `<< 8 = zext 16 (SI `_ record_sz) `|| `( 0 )_ 8); last first.
    rewrite concat_shl.
    apply u2Z_inj.
    rewrite u2Z_castC.
    congr (Z<=u (_ `<< 8)).
    apply u2Z_inj.
    by rewrite (u2Z_zext 24) (u2Z_zext 8) (u2Z_zext 16).
  rewrite s2Z_u2Z_pos'; last first.
    rewrite u2Z_or (u2Z_zext 16).
    split.
      apply addZ_ge0; last by apply min_u2Z.
      apply Z.mul_nonneg_nonneg => //; by apply min_u2Z.
    apply (@ltZ_trans (2 ^^ 8 * 2 ^^ 8 + 2 ^^ 8)%Z) => //.
    apply ltZ_add; last by apply max_u2Z.
    apply ltZ_pmul2r => //; exact: max_u2Z.
  by rewrite u2Z_or (u2Z_zext 16) 2!u2ZE.
Ent_decompose (26 (* Hbu *) :: nil) (0 (* final_bu *) :: nil).
  unfold Hbu, final_bu, Final_bu.
  Ent_R_ex BU2.
  rewrite -[X in X ===> _] coneP.
  apply monotony; last by apply ent_id.
  apply ent_R_sbang.
  by rewrite -the_n_n_SI /u2nat -(addnC '|the_n|) addnC slice_app BU2SI BU2BU1 BU1SI -slice_app.
have SI_sid_BU_51 : SI `_ sid = BU2 `_ 51.
  rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //=.
  - apply leq_ltn_trans with (5 + '| 44 |) => //.
    rewrite ltn_add2l.
    apply/ltP.
    apply Zabs_nat_lt.
    clear -HN1; omega.
  - rewrite leqnn andbC /=.
    apply O_lt_Zabs_nat; omega.
have SI_compmeth_BU_helper :
  4 < compmeth + nat<=u (BU2 `_ 51) + ciph_len_value_nat < 5 + '| the_n |.
  apply/andP; split; first by done.
  apply/ltP; apply Nat2Z.inj_lt.
  rewrite 2!inj_plus [in X in (_ < X)%Z]inj_plus /u2nat Z_of_nat_Zabs_nat; last by apply min_u2Z.
  rewrite Z_of_nat_Zabs_nat; last by clear -HN1; omega.
  rewrite -/the_n_plus5 /ciph_len_value_nat Z_of_nat_Zabs_nat; last by omega.
  exact: compmeth_max.
Ent_L_dup (Hciph_len :: nil).
Ent_L_dup (Hsess_len :: nil).
Ent_decompose (1 (* k < 128 *) :: 2 (* k * 2 < ciph_len *) :: 3 (* Hssl_cipher_i *) :: 4 (* BU2 `_ (54 + nat<=u BU2 `_ 51 + 2 * k) = `( 0 )_8 *) :: 5 (* !b b[(int) __ssl_ciphers_i \= (int) ([ ssl_cipher_i ]8c)]*) :: 27 (* Hciph_len *) :: 30 (* Hsess_len *) :: 32 (* Hses_cipher *) :: nil) (0 (* final_ses*) :: nil).
  apply ent_L_sbang_con => Hk.
  set k_ciph := `! \b _ \< __ciph_len.
  Ent_L_stren_by ( !!(Z<=nat k * 2 < ciph_len_value_Z)%Z ) (Hciph_len :: k_ciph :: nil).
    unfold k_ciph, Hciph_len.
    Ent_LR_rewrite_eq_e O (* ciph_len *).
    Ent_R_subst_apply; Ent_L_subst_apply.
    rewrite -/ciph_len_exp.
    Bbang2sbang.
    apply ent_sbang_sbang.
    move/Zlt_gb. move/(_ erefl erefl).
    have k2_bound : (- 2 ^^ 31 <= Z<=nat k * 2 < 2 ^^ 31)%Z.
      move/ltP : Hk; move/Nat2Z.inj_lt.
      rewrite (_ : Z<=nat 128 = 128%Z) // => Hk.
      simpl expZ; omega.
    rewrite s2Z_ge_s_cst_e; last by exact k2_bound.
    apply; first by omega.
    rewrite -/ciph_len_value_Z [_ ^^ _]/=; omega.
  apply ent_L_sbang_con => k2.
  Ent_L_contract_bbang 0 (* k_ciph *); clear k_ciph.
  Ent_L_contract_bbang 4 (* Hciph_len *).
  unfold final_ses, Final_ses.
  Ent_R_ex i.
  Ent_R_ex k.
  Ent_R_ex (CI `32_ i).
  have Htmp : CI `32_ i = CI `32_ i := erefl. Ent_R_remove_sbang 1 Htmp; clear Htmp.
  unfold Hssl_cipher_i.
  Ent_LR_rewrite_eq_e 0 (* ssl_ciphers_i *).
  Ent_L_subst_apply.
  apply ent_L_sbang_con => Hp0.
  Ent_L_subst_apply.
  Ent_L_subst_apply.
  Ent_LR_subst_inde.
  Ent_R_subst_con_distr.
  Ent_R_subst_apply.
  Ent_LR_subst_inde.
  rewrite /sess_len Z_of_nat_Zabs_nat; last by apply min_u2Z.
  rewrite SI_sid_BU_51 /Hses_cipher (_ : zext 24 (BU2 `_ 51) = `( Z<=u (BU2 `_ 51) )_32 ); last first.
    apply u2Z_inj.
    rewrite (u2Z_zext 24) Z2uK //=.
    split; first by apply min_u2Z.
    apply (@ltZ_trans (2 ^^ 8)%Z) => //; exact: max_u2Z.
  Ent_L_conA. (* TODO: check *)
  apply monotony_R.
  Bbang2sbang.
  rewrite /ssl_cipher_i gb_eq_e ge_cast_sint_cst_8c ge_cast_sint_cst_sint.
  apply ent_L_sbang_con.
  move/eqP/phy_of_si32_inj => CI_i_BU.
  have SI_compmeth_BU :
    SI `_ (compmeth + nat<=u (BU2 `_ 51) + 2 * k + 1) = BU2 `_ (54 + nat<=u BU2 `_ 51 + k * 2 + 1).
    rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //.
    - by rewrite -addnA subnKC mulnC.
    - apply/andP; split; first by done.
      eapply leq_ltn_trans; last by apply SI_compmeth_BU_helper.
      rewrite -addnA leq_add2l -ltnS addn1 ltnS mulnC /ciph_len_value_nat.
      rewrite Z_of_nat_lt Z_of_nat_Zabs_nat; last by omega.
      rewrite inj_mult; exact/ltZP.
    - rewrite leqnn andbC /=.
      apply O_lt_Zabs_nat; omega.
  rewrite SI_compmeth_BU CI_i_BU.
  have SI_compmeth_BU2 : SI `_ (compmeth + nat<=u (BU2 `_ 51) + 2 * k) =
                         BU2 `_ (54 + nat<=u BU2 `_ 51 + 2 * k).
    rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //.
    - apply/andP; split; first by done.
      eapply leq_ltn_trans; last by apply SI_compmeth_BU_helper.
      rewrite leq_add // /ciph_len_value_nat Z_of_nat_le Z_of_nat_Zabs_nat; last by omega.
      rewrite mulnC inj_mult; exact/leZP/ltZW.
    - rewrite leqnn andbC /=.
      apply O_lt_Zabs_nat; omega.
  rewrite SI_compmeth_BU2 Hp0 zext_Z2u // -zext_concat.
  by apply ent_L_bbang, ent_R_sbang.
Ent_decompose (13 (* final_rb *) :: nil) (0 :: nil); first by apply ent_id.
Ent_decompose (13 (* final_id *) :: nil) (0 :: nil); first by apply ent_id.
have nat_the_n : 0 < '| the_n |.
  clear -HN1.
  rewrite (_ : 0 = '| 0 |) //.
  apply/ltP; apply Zabs2Nat.inj_lt; omega.
have SI_min_req_BU_18 : SI `_ min_req = BU2 `_ 18.
  rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //.
  - apply (@leq_ltn_trans (5 + '| 44 |)) => //.
    rewrite ltn_add2l.
    apply/ltP; apply Zabs2Nat.inj_lt; omega.
  - apply/andP; by rewrite leqnn.
have SI_maj_req : SI `_ maj_req = BU2 `_ 17.
  rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //.
  - apply (@leq_ltn_trans (5 + '| 44 |)) => //.
    rewrite ltn_add2l.
    apply/ltP/Zabs2Nat.inj_lt; omega.
  - apply/andP; by rewrite leqnn.
have SI_maj_ver_BU : SI `_ maj_ver = BU1 `_ 9.
  by rewrite /nth' (nth_slices _ _ _ (esym BU1SI)).
have SI_min_ver_BU : SI `_ min_ver = BU1 `_ 10.
  by rewrite /nth' (nth_slices _ _ _ (esym BU1SI)).
Ent_decompose (17 (* Hssl_server *) :: nil) (0 (* final_ssl_context *):: nil).
  unfold Hssl_server, final_ssl_context.
  have -> : si32<=phy ((phyint) SSL_MAJOR_VERSION_3) = zext 24 (SI `_ maj_ver).
    by rewrite SI_maj_ver_BU BU1_9 /safe_cast_phy /si32_of_phy /= i8_of_i32Ko.
  set ca := zext _ (if _ then _ else _).
  have -> : minver_u = ca.
    rewrite /minver_u /minver_exp /ca SI_min_req_BU_18.
    by rewrite si32_of_phy_safe_cast_phy_uchar i8_of_phy_ifte !phy_of_ui8K Z2uK.
  rewrite SI_maj_req -SI_min_req_BU_18; by apply ent_id.
unfold PolarSSLClientHellop.
have -> : SI `_ 0 = S621.handshake.
  have -> : SI `_ 0 = BU1 `_ 8 by rewrite /nth' (nth_slices _ _ _ (esym BU1SI)).
  by case: BU1_8 => _ ->.
rewrite -sbang_con.
Ent_R_flat; apply ent_R_sbang_con => //.
have -> : SI `_ ('| S74.Handshake_hd + 1 |) = BU2 `_ 13.
  rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //.
  apply/andP; split; first by done.
  by rewrite leqnn.
rewrite BU2_13 // -sbang_con.
Ent_R_flat; apply ent_R_sbang_con => //.
have SI_handshake_sz : SI `_ handshake_sz = BU2 `_ 14.
  rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //.
  - apply/andP; split; first by done.
    rewrite (_ : 5 = '| Z<=nat 5 |) // -plusE -Zabs_nat_Zplus //; last by omega.
    rewrite (_ : handshake_sz = '| 6 |) //.
    apply/ltP; apply Zabs_nat_lt => //; omega.
  - by rewrite leqnn andbC.
have -> : SI `_ maj_ver = S621.SSLv30_maj by rewrite SI_maj_ver_BU BU1_9.
rewrite -sbang_con.
Ent_R_flat; apply ent_R_sbang_con => //.
have -> : SI `_ maj_req = S621.SSLv30_maj by rewrite SI_maj_req BU2_17.
rewrite -sbang_con.
Ent_R_flat; apply ent_R_sbang_con => //.
rewrite -sbang_con.
have -> : !!( S621.length_maxp (n' SI) ) <==> emp.
  rewrite /n' /S621.length_maxp /= /S41.bytes2nat /= /MachineIntByte_m.bytes2nat /= /multi_int.bSum_c /=.
  have -> : ('| (u2Zc (SI `_ record_sz) * 256 + u2Zc (SI `_ record_sz.+1)) | = '| the_n |)%Z.
    by rewrite the_n_n_SI /n /= /n' /= /multi_int.bSum_c.
  have -> : '| the_n | <= 2 ^ 14.
    rewrite (_ : 2 ^ 14 = '| (2 ^^ 14) |) //.
    apply/leP; apply Zabs2Nat.inj_le => //.
    omega.
    simpl expZ; omega.
  by apply sbang_emp.
have SI_Shandshake_sz : SI `_ handshake_sz.+1 = BU2 `_ 15.
  rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //.
  - apply/andP; split; first by done.
    rewrite (_ : 5 = '| (Z<=nat 5) |) //.
    rewrite -plusE -Zabs_nat_Zplus //.
    rewrite (_ : handshake_sz.+1 = '| 7 |) //.
    apply/ltP; apply Zabs_nat_lt; omega.
    omega.
  - by rewrite leqnn andbC.
have SI_SShandshake_sz : SI `_ handshake_sz.+2 = BU2 `_ 16.
  rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //.
  - apply/andP; split; first by done.
    rewrite (_ : 5 = '| Z<=nat 5 |) //.
    rewrite -plusE -Zabs_nat_Zplus //.
    rewrite (_ : handshake_sz.+2 = '| 8 |) //.
    apply/ltP; apply Zabs_nat_lt; omega.
    omega.
  - by rewrite leqnn andbC.
have SI_csuites_BU : SI `_ (csuites + nat<=u (BU2 `_ 51)) = BU2 `_ (52 + nat<=u BU2 `_ 51).
  rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //.
  - rewrite (_ : csuites = 44) //.
    apply/andP; split; first by done.
    apply/ltP; apply Nat2Z.inj_lt.
    rewrite 2!inj_plus.
    rewrite {1}/u2nat Z_of_nat_Zabs_nat; last by apply min_u2Z.
    rewrite Z_of_nat_Zabs_nat; last by omega.
    apply: ltZ_trans; last by apply csuites_max.
    rewrite (_ : Z_of_nat 44 = 44%Z) // (_ : Z<=nat csuites.+1 = 45%Z) //.
    rewrite -/(BU2 `_ 51); omega.
  - rewrite leqnn andbC /=.
    apply O_lt_Zabs_nat; omega.
have SI_Scsuites_BU : SI `_ (csuites.+1 + nat<=u BU2 `_ 51) = BU2 `_ (53 + nat<=u BU2 `_ 51).
  rewrite /nth' (nth_slices _ _ _ (esym BU2SI)) //.
  - rewrite (_ : csuites = 44) //.
    apply/andP; split; first by done.
    apply/ltP; apply Nat2Z.inj_lt.
    rewrite 2!inj_plus {1}/u2nat Z_of_nat_Zabs_nat; last by apply min_u2Z.
    rewrite Z_of_nat_Zabs_nat; last by omega.
    apply: leZ_ltZ_trans; last by apply csuites_max.
    exact: leZZ.
  - rewrite leqnn andbC /=.
    apply O_lt_Zabs_nat; omega.
have SI_ciph_len_value_Z : Z<=u (SI `_ (csuites + nat<=u (BU2 `_ 51)) `||
                                 SI `_ (csuites.+1 + nat<=u (BU2 `_ 51))) = ciph_len_value_Z.
  unfold ciph_len_value_Z, ciph_len_value, ciph_len_exp, Shigh, Slow.
  rewrite SI_csuites_BU SI_Scsuites_BU si32_of_phy_gb_or_e ge_cast_sint_cst_8c.
  rewrite [in X in _ = Z<=s ( _ `|` X) ] phy_of_si32K sint_shl_e_to_i32_ge s2Z_u2Z_pos; last first.
    apply/leZP.
    rewrite le0_or //; last by rewrite (s2Z_zext 24) //; apply/leZP/min_u2Z.
    apply/leZP.
    rewrite zext_concat concatA (@s2Z_castA 16 8 8).
    by apply le0concat.
  by rewrite (@u2Z_or 24) u2Z_concat (u2Z_zext 16).
have SI_compmeth_BU : SI `_ (compmeth + nat<=u (BU2 `_ 51) + ciph_len_value_nat) =
                      BU2 `_ (54 + nat<=u BU2 `_ 51 + ciph_len_value_nat).
  rewrite /nth' (@nth_slices _ (8 + 5) '| the_n | SI BU2 5 '| the_n |) //.
  rewrite leqnn andbC /=.
  apply O_lt_Zabs_nat; omega.
have SI_comp_len_value_Z :
    Z<=u (SI `_ (compmeth + nat<=u (BU2 `_ 51) + ciph_len_value_nat)) = Z<=s (si32<=phy comp_len_value).
  rewrite /comp_len_value /comp_len_exp SI_compmeth_BU ge_cast_sint_cst_8c.
  rewrite phy_of_si32K s2Z_u2Z_pos; last by rewrite (s2Z_zext 24) //; apply min_u2Z.
  by rewrite (u2Z_zext 24).
pose comp_len_value_Z := Z<=s (si32<=phy comp_len_value).
pose Hcomp_len_value_Z := !!(1 <= comp_len_value_Z <= 16)%Z.
set Hcomp_len2 := `! \~b \b __comp_len \< [ 1 ]sc \|| __comp_len \> [ 16 ]sc.
Ent_L_stren_by Hcomp_len_value_Z (Hcomp_len :: Hcomp_len2 :: nil).
  rewrite /Hcomp_len.
  Ent_LR_rewrite_eq_e 0.
  Ent_L_subst_apply; Ent_R_subst_apply.
  rewrite -bbang_bneg_or -CgeqNlt sequiv_ge_sym sequiv_gt_sym -CgeqNlt sequiv_ge_sym.
  Bbang2sbang.
  rewrite sbang_con.
  apply ent_sbang_sbang.
  case.
  move/Zle_gb. move/(_ erefl erefl).
  rewrite i32_ge_s_cst_e Z2sK // -/comp_len_value_Z => ?.
  move/Zle_gb. move/(_ erefl erefl).
  by rewrite i32_ge_s_cst_e Z2sK.
rewrite /Hcomp_len_value_Z {Hcomp_len_value_Z}.
apply ent_L_sbang_con => Hcomp_len_value_Z.
pose Hextensions' :=
  !!(Z<=nat compmeth.+1 + Z<=u BU2 `_ 51 + ciph_len_value_Z + Z<=s (si32<=phy (comp_len_value)) =
     the_n_plus5)%Z.
Ent_L_stren_by Hextensions' (Hsess_len ::  Hn_old :: Hciph_len :: Hcomp_len :: Hextensions :: nil).
  unfold Hcomp_len, Hciph_len, Hsess_len, Hn0, Hn_old, Hn, Hextensions.
  Ent_LR_rewrite_eq_e 0 (* comp_len *).
  Ent_R_subst_apply; do 4 Ent_L_subst_apply.
  rewrite -/Hextensions'.
  Ent_LR_rewrite_eq_e 0 (* n_old *).
  Ent_R_subst_apply; do 3 Ent_L_subst_apply.
  rewrite -/Hextensions'.
  Ent_LR_rewrite_eq_e 0 (* ciph_len *).
  do 3 Ent_LR_subst_apply.
  rewrite -/Hextensions'.
  Ent_LR_rewrite_eq_e 0 (* sess_len *).
  do 2 Ent_LR_subst_apply.
  rewrite -/Shigh -/Slow -/ciph_len_exp bneg_neq_eq.
  Bbang2sbang.
  apply ent_sbang_sbang.
  rewrite gb_eq_e.
  move/eqP.
  rewrite -[in X in _ = X -> _](ground_exp_sem (store0 sigma)).
  rewrite -> (@sequiv_add_e_sc_pos _ sigma 5 the_n); last 3 first.
    done.
    omega.
    simpl expZ; omega.
  rewrite -/the_n_plus5.
  rewrite [in X in _ = X -> _](ground_exp_sem (store0 sigma)).
  set lhs := ground_exp _ _.
  set rhs := ground_exp _ _.
  move=> H.
  have {H} : Z<=s (si32<=phy lhs) = Z<=s (si32<=phy rhs) by rewrite H.
  rewrite /lhs /rhs {lhs rhs} si32_of_phy_gb_add_e si32_of_phy_gb_add_e.
  rewrite si32_of_phy_gb_add_e ge_cast_sint_cst_8c (phy_of_si32K (zext 24 BU2`_51)).
  rewrite i32_ge_s_cst_e i32_ge_s_cst_e Z2sK; last by unfold the_n_plus5; simpl expZ; omega.
  move=> <-.
  rewrite -/ciph_len_value /comp_len_value ge_cst_e -/comp_len_value (_ : Z<=nat _ = 47%Z) //.
  move: (min_u2Z (BU2 `_ 51)) (max_u2Z (BU2 `_ 51)) => BU51max.
  rewrite s2Z_add; last first.
    rewrite -/comp_len_value_Z s2Z_add; last first.
      rewrite -/ciph_len_value_Z s2Z_add; rewrite Z2sK // (s2Z_zext 24) //; simpl expZ; omega.
    rewrite -/ciph_len_value_Z s2Z_add; rewrite Z2sK // (s2Z_zext 24) //; simpl expZ; omega.
  rewrite s2Z_add; last first.
    rewrite -/ciph_len_value_Z s2Z_add; rewrite Z2sK // (s2Z_zext 24) //; simpl expZ; omega.
  rewrite -/ciph_len_value_Z s2Z_add; last by rewrite Z2sK // (s2Z_zext 24) //; simpl expZ; omega.
  by rewrite Z2sK // (s2Z_zext 24).
apply ent_L_sbang_con => Hextensions''.
clear Hextensions'.
Ent_L_contract_bbang 16 (* Hextensions *); clear Hextensions.
rewrite coneP.
Ent_L_dup (Hn0 :: Hn :: Hm :: nil).
rewrite -sbang_con.
Ent_decompose (13 (* Hn0 *) :: 10 (* Hn *) :: 7 (* Hm *) :: nil) (0 (* length_maxp *) :: nil).
  unfold Hn0, Hn, Hm.
  Ent_LR_rewrite_eq_e 0 (* n0 *).
  do 3 Ent_LR_subst_apply.
  Ent_LR_rewrite_eq_e 0 (* n *).
  Ent_R_subst_apply; Ent_L_subst_apply.
  rewrite -the_n_n_SI in_left2_n5 /the_n_plus5 (_ : `( 5 + the_n )_32 = Z2s 32 (5 + the_n)); last first.
    apply s2Z_inj.
    rewrite s2Z_u2Z_pos'; last first.
      split; first by apply min_u2Z.
      rewrite Z2uK; last by simpl expZ; omega.
      simpl expZ; omega.
    rewrite Z2uK; last by simpl expZ; omega.
    rewrite Z2sK //; by simpl expZ; omega.
  Bbang2sbang.
  rewrite -(ground_bexp_sem (store0 sigma)).
  rewrite (@sequiv_sub_e_sc _ sigma); last 3 first.
    simpl expZ; omega.
    done.
    simpl expZ; omega.
  rewrite (_ : 5 + the_n - 5 = the_n)%Z; last by omega.
  rewrite (ground_bexp_sem (store0 sigma)) gb_eq_e.
  apply ent_sbang_sbang.
  move/eqP.
  set lhs := [ _ ]ge.
  set rhs := [ _ ]ge.
  move=> abs; have {abs} : si32<=phy lhs = si32<=phy rhs. by rewrite abs.
  rewrite /lhs /rhs {lhs rhs} i32_ge_s_cst_e.
  set lhs := Z2s _ _.
  set rhs := si32<=phy _.
  move=> abs; have {abs} : s2Z lhs = s2Z rhs. by rewrite abs.
  rewrite Z2sK; last by simpl expZ; omega.
  move=> K; rewrite K; rewrite /rhs /lhs.
  rewrite si32_of_phy_gb_add_e s2Z_add; last first.
    rewrite s2Z_ge_s_cst_e // si32_of_phy_gb_or_e sint_shl_e_to_i32_ge -SI_Shandshake_sz -SI_SShandshake_sz.
    have Htmp2 : (0 <= Z<=u SI `_ handshake_sz.+1 * 2 ^^ 8 +
      Z<=u SI `_ handshake_sz.+2 < 2 ^^ predn 32)%Z.
      split.
        apply/addZ_ge0; last by apply min_u2Z.
        apply/mulZ_ge0 => //; by apply min_u2Z.
      apply (@ltZ_trans (2 ^^ 8 * 2 ^^ 8 + 2 ^^ 8)%Z) => //.
      apply ltZ_add; last by apply max_u2Z.
      by apply ltZ_pmul2r => //; apply max_u2Z.
    rewrite s2Z_u2Z_pos'; last first.
      rewrite ge_cast_sint_cst_8c phy_of_si32K (u2Z_or (zext 16 SI `_ handshake_sz.+1)) u2Z_zext; exact Htmp2.
    rewrite ge_cast_sint_cst_8c phy_of_si32K (u2Z_or (zext 16 SI `_ handshake_sz.+1)) u2Z_zext.
    split.
      apply (@leZ_trans Z0) => //.
      apply addZ_ge0 => //.
      apply addZ_ge0; last by apply min_u2Z.
      apply mulZ_ge0 => //; by apply min_u2Z.
    apply (@ltZ_trans (4 + (2 ^^ 8 * 2 ^^ 8 + 2 ^^ 8))%Z) => //.
    apply leZ_lt_add => //.
    apply ltZ_add; last exact: max_u2Z.
    by apply ltZ_pmul2r => //; apply max_u2Z.
  rewrite s2Z_ge_s_cst_e // si32_of_phy_gb_or_e sint_shl_e_to_i32_ge.
  set tmp2 := Z<=s _.
  have Htmp2 : (0 <= tmp2)%Z.
    apply/leZP.
    apply le0_or.
    rewrite zext_concat.
    apply/leZP.
    rewrite concatA (@s2Z_castA 16 8 8).
    by apply le0concat.
    rewrite ge_cast_sint_cst_8c phy_of_si32K (s2Z_zext 24) //.
    exact/leZP/min_u2Z.
  rewrite Zabs2Nat.inj_add; last 2 first.
    done.
    exact Htmp2.
  rewrite (_ : Pos.to_nat 4 = '| 4 |) // plusE.
  apply leq_add; first by apply leqnn.
  unfold m.
  apply/leP/Zabs2Nat.inj_le.
    rewrite multi_int.bSum_c_Sum; by apply multi_int.min_lSum.
  exact Htmp2.
  rewrite /m' /= /multi_int.bSum_c /= -!u2ZE SI_handshake_sz BU2_14 /tmp2 Z2uK //=.
  apply Zeq_le.
  rewrite s2Z_u2Z_pos; last by rewrite -/tmp2; exact Htmp2.
  by rewrite ge_cast_sint_cst_8c phy_of_si32K (@u2Z_or 24) SI_Shandshake_sz (u2Z_zext 16) SI_SShandshake_sz.
rewrite -sbang_con.
have -> : !!( (Z<=nat (sess_len SI) <= tls_max S7412.SessionID)%Z ) <==> emp.
  rewrite /sess_len SI_sid_BU_51 Z_of_nat_Zabs_nat; last by apply min_u2Z.
  by apply sbang_emp.
Ent_R_flat.
rewrite -sbang_con.
have -> : !!( (tls_min S7412.cipher_suites_type <= Z<=nat (ciph_len SI) <=
               tls_max S7412.cipher_suites_type)%Z) <==> emp.
  (* csuites = 44 *)
  rewrite /ciph_len /sess_len SI_sid_BU_51 Z_of_nat_Zabs_nat; last by apply min_u2Z.
  rewrite SI_ciph_len_value_Z.
  apply sbang_emp.
  simpl (tls_min S7412.cipher_suites_type); simpl (tls_max S7412.cipher_suites_type); omega.
Ent_R_flat.
rewrite -sbang_con.
Ent_decompose (18 (* Hciph_len *) :: 19 (* Hciph_len_even *) :: nil) (0 (* even (ciph_len SI) *) :: nil).
  unfold Hciph_len, Hciph_len_even.
  Ent_L_ex k'.
  Ent_LR_rewrite_eq_e 1 (* ciph_len *) . (* CHECK: fait un simpl indesirable *)
  do 2 Ent_L_subst_apply.
  apply ent_L_sbang_con2 => Hk'.
  Ent_R_subst_apply.
  Bbang2sbang.
  apply ent_sbang_sbang.
  rewrite gb_eq_e.
  move/eqP => X.
  rewrite /ciph_len /sess_len SI_sid_BU_51 SI_csuites_BU SI_Scsuites_BU.
  set lhs := ground_exp (_ \| _) _ in X.
  suff : ~~ odd (nat<=u (si32<=phy lhs)).
    rewrite /lhs si32_of_phy_gb_or_e sint_shl_e_to_i32_ge /u2nat ge_cast_sint_cst_8c.
    by rewrite phy_of_si32K (@u2Z_or 24) u2Z_concat (u2Z_zext 16).
  rewrite -X i32_ge_s_cst_e /u2nat -s2Z_u2Z_pos; last first.
    rewrite Z2sK; [omega | simpl expZ; omega].
  rewrite Z2sK; last by simpl expZ; omega.
  by rewrite Zabs_nat_mult muln2 odd_double.
have comp_len_SI : comp_len SI = nat<=s (si32<=phy comp_len_value).
  rewrite /s2nat -SI_comp_len_value_Z /comp_len /sess_len SI_sid_BU_51.
  rewrite /ciph_len /ciph_len_value_nat.
  by rewrite -SI_ciph_len_value_Z /sess_len SI_sid_BU_51.
rewrite -sbang_con -conA.
apply ent_R_sbang_con.
  rewrite comp_len_SI Z_of_nat_Zabs_nat; rewrite -/comp_len_value_Z; omega.
rewrite -sbang_con -[in X in _ ===> X] conA.
apply ent_R_sbang_con.
  move: HSI_new; clear -the_n_n_SI HN1.
  rewrite /the_n_plus5 Zabs2Nat.inj_add //; last by omega.
  by rewrite the_n_n_SI addnC.
Ent_decompose (7 (* Hm *) :: 9 (* Hn*) :: 11 (* Hn0 *) :: nil) (0 :: nil).
  unfold Hm, Hn, Hn0, S7412.client_extensions_present, m, sess_len, ciph_len, comp_len, sess_len.
  rewrite SI_sid_BU_51 {2}/u2nat SI_ciph_len_value_Z.
  rewrite /ciph_len /sess_len SI_sid_BU_51 {4}/u2nat SI_ciph_len_value_Z.
  fold ciph_len_value_nat.
  rewrite {2}/u2nat SI_comp_len_value_Z -/comp_len_value_Z /S7412.ClientHello_sz.
  rewrite [fixed_sz S7412.cipher_suites_type]/= [fixed_sz S7412.compression_methods_type]/=.
  rewrite /S7412.Hello_sz [fixed_sz S621.ProtocolVersion]/=.
  rewrite [fixed_sz S7412.Random]/= [fixed_sz S7412.SessionID]/=.
  rewrite {1}/u2nat Z_of_nat_Zabs_nat; last by apply min_u2Z.
  rewrite /multi_int.bSum_c [foldl _ _ _]/= SI_handshake_sz SI_Shandshake_sz SI_SShandshake_sz.
  rewrite -!u2ZE BU2_14 Z2uK // mul0Z add0Z.
  set lock := !!( _ ).
  Ent_LR_rewrite_eq_e 0.
  do 3 Ent_LR_subst_apply.
  rewrite -/lock.
  Ent_LR_rewrite_eq_e 1.
  do 2 Ent_LR_subst_apply.
  rewrite -/lock in_left2_n5 /lock.
  Bbang2sbang.
  apply ent_sbang_sbang.
  rewrite gb_eq_e.
  move/eqP.
  rewrite (_ : [_ \- _]ge = [ Z2u 32 the_n ]p); last first.
    rewrite -(ground_exp_sem (store0 sigma)).
    rewrite (_ : [ `( the_n_plus5 )_32 ]pc = [ the_n_plus5 ]sc :> exp _ (ityp: sint)); last first.
      congr ([ _ ]pc).
      rewrite Z2s_Z2u_k //.
      simpl expZ; unfold the_n_plus5; omega.
    rewrite sequiv_sub_e_sc; last 3 first.
      simpl expZ; unfold the_n_plus5; omega.
      done.
      simpl expZ; unfold the_n_plus5; omega.
    rewrite /the_n_plus5 (_ : 5 + the_n - 5 = the_n)%Z; last by ring.
    rewrite (ground_exp_sem (store0 sigma)).
    apply si32_of_phy_inj.
    rewrite i32_ge_s_cst_e phy_of_si32K Z2s_Z2u_k //.
    simpl expZ; unfold the_n_plus5; omega.
  set lhs := [ _ ]ge.
  set rhs := [ `( the_n )_32 ]p.
  move=> abs; have {abs} : si32<=phy lhs = si32<=phy rhs by rewrite abs.
  rewrite {}/lhs {}/rhs (phy_of_si32K (`( the_n )_32)) si32_of_phy_gb_add_e.
  set lhs := _ `+ _.
  move=> abs; have {abs} : u2Z lhs = the_n.
    rewrite abs Z2uK //.
    simpl expZ; omega.
  rewrite {}/lhs.
  set tmp := [ _ \| _ ]ge.
  have tmptmp : u2Z (si32<=phy tmp) = (Z<=u BU2`_15 * 256 + Z<=u BU2`_16)%Z.
    rewrite {} /tmp si32_of_phy_gb_or_e sint_shl_e_to_i32_ge.
    by rewrite ge_cast_sint_cst_8c phy_of_si32K (@u2Z_or 24) (u2Z_zext 16).
  rewrite [in X in _ -> _ = X]Z_of_nat_Zabs_nat; last first.
    apply addZ_ge0; last exact: min_u2Z.
    apply mulZ_ge0 => //; exact: min_u2Z.
  rewrite -tmptmp i32_ge_s_cst_e.
  rewrite u2Z_add; last first.
    rewrite Z2s_Z2u_k // Z2uK // tmptmp.
    apply (@ltZ_trans (4 + 2 ^^ 16 + 2 ^^ 8)%Z) => //.
    rewrite -addZA ltZ_add2l.
    apply ltZ_add; last exact: max_u2Z.
    rewrite (_ : 2 ^^ 16 = 2 ^^ 8 * 2 ^^ 8)%Z //.
    apply ltZ_pmul2r => //; exact/max_u2Z.
  rewrite Z2s_Z2u_k // Z2uK //.
  move=> Htmptmp.
  rewrite /the_n_plus5 -Htmptmp (_ : Z<=nat _ = 47%Z) // in Hextensions''.
  rewrite (_ : Z<=nat 1 = 1%Z) // (_ : Z<=nat 2 = 2%Z) // Z_of_nat_Zabs_nat; last by omega.
  rewrite -/comp_len_value_Z in Hextensions''.
  clear -Hextensions'' Hciph_len_bound_Z.
  rewrite (_ : Z<=nat ciph_len_value_nat = ciph_len_value_Z); last first.
    rewrite /ciph_len_value_nat Z_of_nat_Zabs_nat //; omega.
  omega.
Ent_L_contract_bbang 0.
apply ent_L_sbang_con => i_CI.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 0.
Ent_L_contract_bbang 1.
Ent_L_contract_bbang 1.
by apply ent_id.
Qed.

End POLAR_parse_client_hello_triple.

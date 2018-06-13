(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
Require Import ssreflect ssrbool eqtype.
Require Import ZArith_ext Lists_ext String_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_expr C_bipl C_cmd C_seplog.
Require Import POLAR_library_functions.

Local Open Scope C_expr_scope.
Local Open Scope C_cmd_scope.

Section asn1_get_len_prg.

Variable g : Ctxt.t.

Definition POLARSSL_ERR_ASN1_OUT_OF_DATA : value g := [ 20 ]s.
Definition POLARSSL_ERR_ASN1_INVALID_LENGTH : value g := [ 24 ]s.

Local Coercion var_e_coercion := @var_e g.

Definition asn1_get_len : @while.cmd cmd0 (bexp g) := (
  (*
   * int asn1_get_len(uchar **p, uchar *end, int *len)
   *
   *)

  (* if ((end - *p) < 1) { NG } else { OK } *)
  "_p_" <-* "p" ;
  If "end" \-p "_p_" \<e [ 1 ]s Then
    "ret" <- POLARSSL_ERR_ASN1_OUT_OF_DATA ;
    ret
  Else
    (* if (( **p & 0x80) == 0) { *len = *( *p)++; } { ... } *)
    "_c_" <-* "_p_" ;
    If ("_c_" \& [ 128 ]s) \= [ 0 ]s Then
      "_len0_" <-* "_p_" ;
      "len" *<- "_len0_" ;
      "_p1_" <- "_p_" \+p [ 1 ]s ;
      "p" *<- "_p1_" ;
      (* if ( *len > (int) (end - *p)) { NG } { OK } *)
      If "end" \-p "_p1_" \<e "_len0_" Then
        "ret" <- POLARSSL_ERR_ASN1_OUT_OF_DATA ;
        ret
      Else
        "ret" <- [ 0 ]s ;
        ret
    Else
      (* switch ( **p & 0x7F ) { case 1: ... case 2: ... default: ... } *)
      "_n_" <- "_c_" \& [ 127 ]s ;
      If "_n_" \= [ 1 ]s Then
        (* case 1: *)
        (* if (( end - *p ) < 2) { NG } { OK } *)
        If "end" \-p "_p_" \<e [ 2 ]s Then
          "ret" <- POLARSSL_ERR_ASN1_OUT_OF_DATA ;
          ret
        Else
          (* *len = ( *p)[1]; ( *p) += 2; *)
          "_len1_" <-* "_p_" \+p [ 1 ]s ;
          "len" *<- "_len1_" ;
          "_p2_" <- "_p_" \+p [ 2 ]s ;
          "p" *<- "_p2_" ;

          (* if ( *len > (int) (end - *p)) { NG } { OK } *)
          If "end" \-p "_p2_" \<e "_len1_" Then
            "ret" <- POLARSSL_ERR_ASN1_OUT_OF_DATA ;
            ret
          Else
            "ret" <- [ 0 ]s ;
            ret
      Else
       (* not case 1: *)
      If "_n_" \= [ 2 ]s Then
        (* case 2: *)
        (* if (( end - *p ) < 3) { NG } { OK } *)
        If "end" \-p "_p_" \<e [ 3 ]s Then
          "ret" <- POLARSSL_ERR_ASN1_OUT_OF_DATA ;
          ret
        Else
          (* *len = ( *p)[1] << 8 | ( *p)[2]; ( *p) += 3; *)
          "_len2_" <-* "_p_" \+p [ 1 ]s ;
          "_len3_" <-* "_p_" \+p [ 2 ]s ;
          "_len4_" <- ("_len2_" \<<e [ 8 ]s) \| "_len3_" ;
          "len" *<- "_len4_" ;
          "_p3_" <- "_p_" \+p [ 3 ]s ;
          "p" *<- "_p3_" ;

          (* if ( *len > (int) (end - *p)) { NG } { OK } *)
          If "end" \-p "_p3_" \<e "_len4_" Then
            "ret" <- POLARSSL_ERR_ASN1_OUT_OF_DATA ;
            ret
          Else
            "ret" <- [ 0 ]s ;
            ret
      Else (* default: *)
        "ret" <- POLARSSL_ERR_ASN1_INVALID_LENGTH ;
        ret
      )%string.

End asn1_get_len_prg.

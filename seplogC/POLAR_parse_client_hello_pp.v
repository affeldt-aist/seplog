From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
Require Import machine_int seq_ext ssrZ ZArith_ext String.
Import MachineInt.
Require Import C_pp.
Require Import POLAR_parse_client_hello.
Require Import POLAR_library_functions POLAR_library_functions_pp.

Import C_LittleOp_m.
Local Open Scope string_scope.
Local Open Scope zarith_ext_scope.

Set Printing Depth 1000.

Fixpoint int_break_Z2u n (v : Z) (k q : nat) : (Z * seq.seq (int k)) :=
  if q is q'.+1
    then let (v', r) := int_break_Z2u (subn n k) v k q' in
         let (v'', r') := Z.div_eucl v' (2 ^^ k) in
         (v'', Z2u k r' :: r)
    else (v, [::]).

Local Open Scope machine_int_scope.

Lemma int_break_Z2u_computable' :
  forall n (v : Z) (Hv : 0 <= v) k q (H : n = (muln q k.+1)),
  (v / (2 ^^ muln q k.+1), @int_break n k.+1 q H (Z2u n v)) =
  int_break_Z2u n v k.+1 q.
Proof.
  move => n v Hv k q; elim: q k n v Hv.
  - move => k n v Hv H /=.
    rewrite Zdiv_1_r; congr pair.
    move: H (H).
    rewrite {1}mul0n => H H0; subst.
    apply size0nil.
    apply size_int_break.
  - move => q IH k n v Hv H; move: H (H).
    rewrite {1}mulSn.
    move/(f_equal (fun x => x - (k.+1))%nat).
    rewrite addKn => H H0.
    rewrite -H0 /= -IH //.
    move: (Z_div_mod (v / 2 ^^ (q * k.+1)) (2 ^^ k.+1)).
    case: (Z.div_eucl _ _) => a b; case.
    - apply Z.lt_gt, expZ_gt0.
    - move => H1 H2; congr pair.
      - rewrite H0 mulSn addnC ZpowerD -Zdiv_Zdiv; try by apply expZ_ge0.
        rewrite H1 Z.mul_comm Z_div_plus_full_l.
        - by rewrite Z.div_small // addZ0.
        - apply ssrfun.nesym, Z.lt_neq, expZ_gt0.
    - rewrite int_break_cons //.
      congr cons.
        apply u2Z_inj.
        rewrite u2Z_Z2u_Zmod; last first.
          apply Z.div_pos; by [apply min_u2Z | apply expZ_gt0].
        symmetry.
        rewrite u2Z_Z2u_Zmod; last by case: H2.
        rewrite -(Z_mod_plus _ a); last by apply Z.lt_gt, expZ_gt0.
        rewrite mulZC addZC -H1 H u2Z_Z2u_Zmod; last by assumption.
        apply eqmod_Zmod2.
        exact: expZ_ge0.
        red.
        rewrite {1}(Z_div_mod_eq v (2 ^^ n)); last by apply Z.lt_gt, expZ_gt0.
        rewrite {1}H0 mulSn ZpowerD mulZC mulZA.
        rewrite Z_div_plus_full_l; last by apply not_eq_sym, ltZ_eqF, expZ_gt0.
        exists (v / 2 ^^ n); ring.
      congr int_break.
      apply u2Z_inj.
      rewrite u2Z_Z2u_Zmod; last by apply min_u2Z.
      symmetry.
      rewrite u2Z_Z2u_Zmod //.
      symmetry.
      rewrite u2Z_Z2u_Zmod //.
      symmetry.
      rewrite {1}(Z_div_mod_eq v (2 ^^ n)); last by apply Z.lt_gt, expZ_gt0.
      rewrite {1}H0 mulSn ZpowerD -H.
      rewrite mulZC mulZA addZC Z_mod_plus //.
      by apply Z.lt_gt, expZ_gt0.
Qed.

Lemma int_break_Z2u_computable n v (Hv : 0 <= v) k q (H : n = (muln q k.+1)) :
  @int_break n k.+1 q H (Z2u n v) = snd (int_break_Z2u n v k.+1 q).
Proof. by rewrite -int_break_Z2u_computable'. Qed.

Axiom PrintAxiom : forall A, A -> Set.

Eval compute in pp_ctxt.
Eval compute in (foldl
  (fun s p => s ++ typ_to_string (C_types.Ctyp.ty _ (snd p)) (fst p) (line ";"))
  "" sigma).

Goal PrintAxiom _ (pp_cmd 0 ssl_parse_client_hello "").
Proof.
  rewrite /ssl_parse_client_hello /ssl_parse_client_hello1
          /ssl_parse_client_hello2 /ssl_parse_client_hello3
          /ssl_parse_client_hello4 /ssl_parse_client_hello5 /=.
  rewrite /pp_cmd /=.
  rewrite ?pp_cmd_ssl_fetch_input ?pp_cmd_memcpy ?pp_cmd_memset
          ?pp_cmd_md5_update ?pp_cmd_sha1_update /=.
  rewrite !Z2s_2complement // /C_value.phy_of_ui32 /C_value.i8_of_i32 /=.
  rewrite !int_break_Z2u_computable //=.
  compute -[pp_Z append Z.add Z.sub Z.mul Z.leb].
  rewrite ?Z2uK //=.
  lazy.
Abort.

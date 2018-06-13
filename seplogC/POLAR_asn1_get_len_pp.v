Require Import ssreflect ssrbool.
Require Import machine_int.
Import MachineInt.
Require Import C_pp.
Require Import POLAR_asn1_get_len.

Set Printing Width 99999.
Set Printing Depth 99999.

Goal pp_cmd PolarSSL.asn1_get_len "" = "_p_ = *(p); if ((_Bool)(((end - _p_)) < (1))) { ret = 20; ; } else { _c_ = *(_p_); if ((_Bool)(((_c_) & (128)) == (0))) { _len0_ = *(_p_); *(len) = _len0_; _p1_ = (_p_) + (1); *(p) = _p1_; if ((_Bool)(((end - _p1_)) < (_len0_))) { ret = 20; ; } else { ret = 0; ; } } else { _n_ = (_c_) & (127); if ((_Bool)((_n_) == (1))) { if ((_Bool)(((end - _p_)) < (2))) { ret = 20; ; } else { _len1_ = *((_p_) + (1)); *(len) = _len1_; _p2_ = (_p_) + (2); *(p) = _p2_; if ((_Bool)(((end - _p2_)) < (_len1_))) { ret = 20; ; } else { ret = 0; ; } } } else { if ((_Bool)((_n_) == (2))) { if ((_Bool)(((end - _p_)) < (3))) { ret = 20; ; } else { _len2_ = *((_p_) + (1)); _len3_ = *((_p_) + (2)); _len4_ = ((_len2_) << (8)) | (_len3_); *(len) = _len4_; _p3_ = (_p_) + (3); *(p) = _p3_; if ((_Bool)(((end - _p3_)) < (_len4_))) { ret = 20; ; } else { ret = 0; ; } } } else { ret = 24; ; } } } }"%string.
Proof.
rewrite //=.
rewrite /pp_sint /pp_binop /zero32 /one32 !Z2sK //=.
Qed.

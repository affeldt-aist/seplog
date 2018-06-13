From mathcomp Require Import ssreflect ssrbool seq.
Require Import ZArith_ext String_ext.
Require Import machine_int.
Import MachineInt.
Require Import C_types C_types_fp C_value C_expr C_seplog C_pp.

Local Open Scope C_types_scope.

Module C_Env <: CENV.
Definition flds := (("a", ityp uint) :: ("b", ityp uint) :: nil)%string.
Definition g := \wfctxt{ "pair" |> flds \, \O \}.

Definition pair_tg := mkTag "pair".
Definition pair_ab := g.-typ: styp pair_tg.

Definition sigma : g.-env := ("a_pair"%string, pair_ab) :: ("x"%string, g.-ityp: uint) :: ("y"%string, :* (g.-ityp: uint)) :: ("z"%string, :* (:* (g.-ityp: uint))) :: nil. 
Definition uniq_vars : uniq (unzip1 sigma) := Logic.eq_refl.
End C_Env.

Module Import C_m := C_Pp_f C_Env.

Module example_m.

Definition pair_ab_14 := (Z2u 8 0) :: (Z2u 8 0) :: (Z2u 8 0) :: (Z2u 8 1) :: 
                         (Z2u 8 0) :: (Z2u 8 0) :: (Z2u 8 0) :: (Z2u 8 4) :: nil.

Definition var_expr :=  var_e C_Env.sigma "a_pair"%string C_Env.pair_ab refl_equal.

Local Open Scope C_cmd_scope.

Definition x :=  var_e C_Env.sigma "x"%string _ refl_equal.
Definition y :=  var_e C_Env.sigma "y"%string _ refl_equal.
Definition z :=  var_e C_Env.sigma "z"%string _ refl_equal.

Definition test_prog :=
("x" <- [ 0 ]uc; 
"x" <-* ((y) \+ [ 1 ]sc); 
(*z = malloc(1); *)
(z) *<- y(*; 
free(y); 
free(z)*))%string.

End example_m.

Goal (typ_to_string_rec g C_Env.pair_ab "" "" = "struct pair { unsigned int a; unsigned int b; } ")%string.
Proof.
reflexivity.
Qed.

(*
Goal (phyval_to_string _ example_m.pair_ab example_m.pair_ab_14 "" = "{ 1, 4 }")%string.
Proof.
rewrite /example_m.pair_ab /example_m.pair_ab_14 /phyval_to_string //=
  /pp_uint (*/four32 /one32*) //=
  !Z2uK //=.
Qed.
*)

Goal (pp_exp g sigma _ example_m.var_expr "" = "a_pair")%string.
Proof.
reflexivity.
Qed.

(*Goal (pp_cmd example_m.test_prog "" = "x = 0; x = *((y) + (1)); z = malloc(1); *(z) = y; free(y); free(z);")%string.*)

Goal (pp_cmd O example_m.test_prog "" = "x = 0; x = *((y) + (1)); *z = y;")%string.
Proof.
rewrite /pp_cmd.
simpl.
(*rewrite //= /pp_sint /zero32 /one32 !Z2sK //=.
Qed.*)
Abort.

(*
Goal (typ_to_string inplace_reverse_list_m.C_lst "" = "struct C_lst { unsigned int data; struct C_lst * next; }")%string.
Proof.
rewrite //= /struct_tag_to_string /ityp_to_string //=.
Qed.
*)

(*
Goal (pp_exp inplace_reverse_list_m.NULL "" = "(struct C_lst *removeme)(0)")%string.
Proof.
rewrite //=.
rewrite /pp_uint /struct_tag_to_string.
rewrite u2Z_Z2u //=.
split.
- rewrite //=.
- apply Zpower_0.
Qed.
*)

(*
Goal (pp_cmd inplace_reverse_list_m.reverse_list "" = "ret = (struct C_lst *removeme)(0); while (!((_Bool)((i) == ((struct C_lst *removeme)(0))))) { rem = *(&(i->next)); *(&(i->next)) = ret; ret = i; i = rem; }")%string.
Proof.
rewrite //= /pp_uint /struct_tag_to_string u2Z_Z2u //=.
split.
- rewrite //=.
- apply Zpower_0.
Qed.
*)
 
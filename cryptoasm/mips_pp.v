(* seplog (c) AIST 2005-2013. R. Affeldt, N. Marti, et al. GNU GPLv3. *)
(* seplog (c) AIST 2014-2018. R. Affeldt et al. GNU GPLv3. *)
From mathcomp Require Import ssreflect.
Require Import Coq.Program.Wf String Ascii Lia.
Require Import ZArith_ext.
Require Import machine_int.
Import MachineInt.
Require Import sgoto goto compile mips_cmd.
Require Import bbs_prg.

Local Open Scope string_scope.
Local Open Scope zarith_ext_scope.
Local Open Scope machine_int_scope.
Local Open Scope mips_cmd_scope.

(** * a few functions to pretty-print MIPS abstract syntax to conrete syntax;
      application to the BBS PRNG *)

Definition Zdigit_to_Ascii (z : Z) : ascii :=
  match z with
    | 0 => "0"%char
    | 1 => "1"%char
    | 2 => "2"%char
    | 3 => "3"%char
    | 4 => "4"%char
    | 5 => "5"%char
    | 6 => "6"%char
    | 7 => "7"%char
    | 8 => "8"%char
    | 9 => "9"%char
    | _ => ":"%char (* DUMMY *)
  end.

Program Fixpoint positive_to_string_aux (p : positive) (s : string) {measure (nat_of_P p)} : string :=
  let s' := String (Zdigit_to_Ascii (Zpos p mod 10)) s in
    match (Zpos p) / 10 with
      | Zpos q => positive_to_string_aux q s'
      | Z0     => s'
      | _      => ":" (* DUMMY *)
    end.
Next Obligation.
apply nat_of_P_lt_Lt_compare_morphism.
replace ((Pos.compare_cont Eq q p) = Lt) with (Zpos q < Zpos p) by reflexivity.
rewrite Heq_anonymous.
by apply Z_div_lt.
Defined.
Next Obligation.
split; first by done.
congruence.
Defined.

Definition positive_to_string (p : positive) := positive_to_string_aux p "".

Definition Z_to_string_aux (z : Z) (s : string) : string :=
  match z with
    | Zpos p => positive_to_string_aux p s
    | Z0     => String "0" s
    | Zneg p => String "-" (positive_to_string_aux p s)
  end.

Definition Z_to_string (z : Z) : string := Z_to_string_aux z "".

Definition register_to_string_aux (r : reg) (s : string) : string :=
  String "$" (match r with
                | r0 => "0"
                | reg_at   => "at"
                | reg_v0   => "v0"
                | reg_v1   => "v1"
                | reg_a0   => "a0"
                | reg_a1   => "a1"
                | reg_a2   => "a2"
                | reg_a3   => "a3"
                | reg_t0   => "t0"
                | reg_t1   => "t1"
                | reg_t2   => "t2"
                | reg_t3   => "t3"
                | reg_t4   => "t4"
                | reg_t5   => "t5"
                | reg_t6   => "t6"
                | reg_t7   => "t7"
                | reg_s0   => "s0"
                | reg_s1   => "s1"
                | reg_s2   => "s2"
                | reg_s3   => "s3"
                | reg_s4   => "s4"
                | reg_s5   => "s5"
                | reg_s6   => "s6"
                | reg_s7   => "s7"
                | reg_t8   => "t8"
                | reg_t9   => "t9"
                | reg_k0   => "k0"
                | reg_k1   => "k1"
                | reg_gp   => "gp"
                | reg_sp   => "sp"
                | reg_fp   => "fp"
                | reg_ra   => "ra"
              end) ++ s.

Definition register_to_string (r : reg) : string := register_to_string_aux r "".

Definition r2s (r : reg) (s : string) := register_to_string_aux r s.
Definition si2s (i : immediate) (s : string) := Z_to_string_aux (s2Z (sext 16 i)) s.
Definition ui2s (i : immediate) (s : string) := Z_to_string_aux (u2Z (zext 16 i)) s.
Definition sa2s (sa : shifta) (s : string) := Z_to_string_aux (u2Z sa) s.
Definition comma (s : string) := String "," (String " " s).

Definition cmd0_to_string_aux (c : cmd0) (s : string) : string :=
  match c with
    | nop             => "nop" ++ s
    | add     rd rs rt => "add "    ++ (r2s rd (comma (r2s rs (comma (r2s rt s)))))
    | addi    rt rs im => "addi "   ++ (r2s rt (comma (r2s rs (comma (si2s im s)))))
    | addiu   rt rs im => "addiu "  ++ (r2s rt (comma (r2s rs (comma (si2s im s)))))
    | addu    rd rs rt => "addu "   ++ (r2s rd (comma (r2s rs (comma (r2s rt s)))))
    | cmd_and rd rs rt => "and "    ++ (r2s rd (comma (r2s rs (comma (r2s rt s)))))
    | andi    rt rs im => "andi "   ++ (r2s rt (comma (r2s rs (comma (ui2s im s)))))
    | lw      rt ot bs => "lw "     ++ (r2s rt (comma (si2s ot (String "(" (r2s bs (String ")" s))))))
    | lwxs    rd ix bs => "lwxs "   ++ (r2s rd (comma (r2s ix (String "(" (r2s bs (String ")" s)))))) (* Smart MIPS Instr. *)
    | maddu   rs rt    => "maddu "  ++ (r2s rs (comma (r2s rt s)))
    | mflhxu  rd       => "mflhxu " ++ (r2s rd s) (* Smart MIPS Instr. *)
    | mflo    rd       => "mflo "   ++ (r2s rd s)
    | movn    rd rs rt => "movn "   ++ (r2s rd (comma (r2s rs (comma (r2s rt s)))))
    | movz    rd rs rt => "movz "   ++ (r2s rd (comma (r2s rs (comma (r2s rt s)))))
    | mfhi    rd       => "mfhi "   ++ (r2s rd s)
    | mtlo    rd       => "mtlo "   ++ (r2s rd s)
    | mthi    rs       => "mthi "   ++ (r2s rs s)
    | msubu   rs rt    => "msubu "  ++ (r2s rs (comma (r2s rt s)))
    | multu   rs rt    => "multu "  ++ (r2s rs (comma (r2s rt s)))
    | nor     rd rs rt => "nor "    ++ (r2s rd (comma (r2s rs (comma (r2s rt s)))))
    | cmd_or  rd rs rt => "or "     ++ (r2s rd (comma (r2s rs (comma (r2s rt s)))))
    | sll     rd rt sa => "sll "    ++ (r2s rd (comma (r2s rt (comma (sa2s sa s)))))
    | sllv    rd rt rs => "sllv "   ++ (r2s rd (comma (r2s rt (comma (r2s rs s)))))
| sra     rd rt sa => "sra "    ++ (r2s rd (comma (r2s rt (comma (sa2s sa s)))))
    | srl     rd rt sa => "srl "    ++ (r2s rd (comma (r2s rt (comma (sa2s sa s)))))
    | srlv    rd rt rs => "srlv "   ++ (r2s rd (comma (r2s rt (comma (r2s rs s)))))
    | sltu    rd rs rt => "sltu "   ++ (r2s rd (comma (r2s rs (comma (r2s rt s)))))
    | sw      rt ot bs => "sw "     ++ (r2s rt (comma (si2s ot (String "(" (r2s bs (String ")" s))))))
    | subu    rd rs rt => "subu "   ++ (r2s rd (comma (r2s rs (comma (r2s rt s)))))
    | xor     rd rs rt => "xor "    ++ (r2s rd (comma (r2s rs (comma (r2s rt s)))))
    | xori    rt rs im => "xori "    ++ (r2s rt (comma (r2s rs (comma (ui2s im s)))))
  end.

Definition btest_to_string_aux (bt : expr_m.expr_b) (s : string) : string :=
  match bt with
    | expr_m.beq  r1 r2 => r2s r1 (" == " ++ (r2s r2 s))
    | expr_m.bne  r1 r2 => r2s r1 (" <> " ++ (r2s r2 s))
    | expr_m.bltz r     => r2s r (" < 0" ++ s)
    | expr_m.bgez r     => "0 <= " ++ (r2s r s)
    | expr_m.blez r     => r2s r (" <= 0" ++ s)
    | expr_m.bgtz r     => "0 < " ++ (r2s r s)
  end.

Definition btest_to_string (bt : expr_m.expr_b) : string := btest_to_string_aux bt "".

Definition NL : ascii := "010"%char.
Definition NLstr : string := String NL "".
Definition nl (s : string) : string := String NL s.

Definition HT : ascii := "009"%char.
Definition HTstr : string := String HT "".
Definition ht (s : string) : string := String HT s.

Fixpoint cmd_to_string_aux (c : @while.cmd cmd0 expr_m.expr_b) (s : string) : string :=
  match c with
    | while.cmd_cmd0 c        => cmd0_to_string_aux c (nl s)
    | while.seq      c1 c2    => cmd_to_string_aux c1 (cmd_to_string_aux c2 s)
    | while.ifte     bt c1 c2 => "if (" ++ btest_to_string_aux bt (") {" ++ nl (cmd_to_string_aux c1 ("} else {" ++ (nl (cmd_to_string_aux c2 (String "}" (nl s)))))))
    | while.while    bt c     => "while (" ++ btest_to_string_aux bt (") {" ++ nl (cmd_to_string_aux c ("}" ++ (nl s))))
  end.

Definition cmd_to_string (c : @while.cmd cmd0 expr_m.expr_b) : string := cmd_to_string_aux c "".

Require Import mips_seplog.
Module Import compile_m := Compile WMIPS_Hoare.
Import sgoto_hoare_m.
Import sgoto_m.
Import goto_deter_m.
Import goto_m.

Definition lbl (l : label) (s : string) : string := String "L" (Z_to_string_aux (Z_of_nat l) s).

Fixpoint scode_to_string_aux (sc : scode) (s : string) : string :=
  match sc with
    | sO                        => s
    | sC l c                    => lbl l (String ":" (ht (cmd0_to_string_aux c (nl s))))
    | sB l (jmp d)              => lbl l (String ":" (ht ("b "    ++ (lbl d (nl s)))))
    | sB l (cjmp (expr_m.beq r1 r2) d) => lbl l (String ":" (ht ("beq "  ++ r2s r1 (comma (r2s r2 (comma (lbl d (nl s))))))))
    | sB l (cjmp (expr_m.bne r1 r2) d) => lbl l (String ":" (ht ("bne "  ++ r2s r1 (comma (r2s r2 (comma (lbl d (nl s))))))))
    | sB l (cjmp (expr_m.bltz r) d)    => lbl l (String ":" (ht ("bltz " ++ r2s r (comma (lbl d (nl s))))))
    | sB l (cjmp (expr_m.bgez r) d)    => lbl l (String ":" (ht ("bgez " ++ r2s r (comma (lbl d (nl s))))))
    | sB l (cjmp (expr_m.blez r) d)    => lbl l (String ":" (ht ("blez " ++ r2s r (comma (lbl d (nl s))))))
    | sB l (cjmp (expr_m.bgtz r) d)    => lbl l (String ":" (ht ("bgtz " ++ r2s r (comma (lbl d (nl s))))))
    | sS c1 c2                  => scode_to_string_aux c1 (scode_to_string_aux c2 s)
  end.

Definition scode_to_string (sc : scode) : string := scode_to_string_aux sc "".

Definition bbs_cmd := bbs reg_at reg_v0 reg_v1 reg_a0 reg_a1 reg_a2 reg_a3 reg_t0 reg_t1 reg_t2 reg_t3 reg_t4 reg_t5 reg_t6 reg_t7 reg_s0 reg_s1 reg_s2 reg_s3 reg_s4 reg_s5 reg_s6 reg_s7 reg_t8 reg_t9.

Definition compiled_bbs := compile_f 0%nat bbs_cmd.

Lemma ui2s_Z2u : forall z, 0 <= z < 2 ^^ 16 -> ui2s (Z2u 16 z) = Z_to_string_aux z.
Proof.
rewrite /ui2s => z H.
replace (fun s => Z_to_string_aux (u2Z (zext 16 (Z2u 16 z))) s) with (Z_to_string_aux (u2Z (zext 16 (Z2u 16 z)))) => //.
by rewrite u2Z_zext Z2uK.
Qed.

Lemma si2s_Z2s : forall z, - 2 ^^ 15 <= z < 2 ^^ 15 -> si2s (Z2s 16 z) = Z_to_string_aux z.
Proof.
rewrite /si2s => z H.
replace (fun s => Z_to_string_aux (s2Z (sext 16 (Z2s 16 z))) s) with (Z_to_string_aux (s2Z (sext 16 (Z2s 16 z)))) => //.
by rewrite sext_s2Z Z2sK.
Qed.

Lemma si2s_Z2u : forall z, 0 <= z < 2 ^^ 15 -> si2s (Z2u 16 z) = Z_to_string_aux z.
Proof.
rewrite /si2s => z H.
replace (fun s : string => Z_to_string_aux (s2Z (sext 16 (Z2u 16 z))) s) with (Z_to_string_aux (s2Z (sext 16 (Z2u 16 z)))) => //.
f_equal.
rewrite sext_s2Z s2Z_u2Z_pos' Z2uK //; simpl in *; lia.
Qed.

Set Printing Width 99999.
Set Printing Depth 99999.

Goal exists s, scode_to_string compiled_bbs = s.
  set sc := compiled_bbs.
  vm_compute in sc.
  subst sc.
  rewrite /scode_to_string //=.
  rewrite !ui2s_Z2u //= !si2s_Z2s //= !si2s_Z2u //= /r2s //=.
  vm_compute.
  match goal with
    |- (exists s, ?X = s) => idtac X
  end.
Abort.

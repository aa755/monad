Set Default Goal Selector "!".

(*
  Minimal reproduction for BRiCk issue #140.

  This file is intentionally stand-alone: the C++ program is embedded with
  [cpp.prog ... cpp:{{ ... }}] instead of using a separately generated AST file.
  That makes it easier to paste into an upstream BRiCk test.

  The embedded C++ function contains only the heterogeneously typed compound
  addition from the issue:

<<
byte len = 16;
len += 32;
return len;
>>

  The generated AST casts the initializer [16] to [unsigned char], but leaves
  the compound assignment as a mixed arithmetic operation:

<<
Eassign_op Badd (Evar "len" Tuchar) (Eint 32 Tint) Tuchar
>>

  Current upstream automation handles this mixed arithmetic case directly, so
  the proof below no longer needs the old concrete axiom for
  [operators.wp_eval_binop.body ... Badd Tuchar Tint Tuchar 16 32].
*)

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.

Import linearity.
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.

cpp.prog source prog cpp:{{
  namespace minimalexamples {
    using byte = unsigned char;

    byte add_16_32() {
      byte len = 16;
      len += 32;
      return len;
    }
  }
}}.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : source ⊧ CU}.

  cpp.spec "minimalexamples::add_16_32()" as add_16_32_spec with (
    \post [Vint 48] emp
  ).

  Lemma add_16_32_proof :
    verify?[source] add_16_32_spec.
  Proof using MODd.
    verify_spec.
    go.
  Qed.
End with_Sigma.

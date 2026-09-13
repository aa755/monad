(** Minimal scalar byte-write/typed-read example for BRiCk #156.
    The original integer's type witness is kept across the writes. *)
From Stdlib Require Import List NArith ZArith.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import monad.brickmisc.upstream.scalar_bytes.
Import ListNotations linearity.
Set Default Goal Selector "!".
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.
Remove Hints _at_pick_cfrac_and_split_C _at_pick_frac_and_split_C
  _at_split_specific_cfrac_C _at_split_specific_frac_C
  : db_skylabs_syntactic.

cpp.prog source prog cpp:{{
  unsigned int scalar_byte_write() {
    unsigned int x = 0;
    auto p = reinterpret_cast<unsigned char *>(&x);
    p[0] = 4;
    p[1] = 3;
    p[2] = 2;
    p[3] = 1;
    return x;
  }
}}.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : source ⊧ CU}.

  Lemma word_bytes q value bytes :
    decodes Little Unsigned bytes value ->
    length bytes = 4%nat ->
    uintR q value -|-
      type_ptrR Tuint **
      arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes.
  Proof using MODd.
    intros Hdecode Hlength.
    apply scalar_bytes_exact; last exact Hlength.
    unfold decodes_uint.
    rewrite (genv_byte_order_tu source CU MODd).
    exact Hdecode.
  Qed.

  Lemma zero_word_bytes :
    uintR 1$m 0 -|-
    type_ptrR Tuint **
    arrayR Tuchar (fun b : N => primR Tuchar 1$m (Vn b)) [0%N;0%N;0%N;0%N].
  Proof using MODd.
    exact (word_bytes 1$m 0 [0%N; 0%N; 0%N; 0%N]
      ltac:(split;
        [ repeat (apply List.Forall_cons; [rewrite -has_int_type; done | ]);
          apply List.Forall_nil
        | rewrite z_to_bytes._Z_from_bytes_eq; reflexivity ])
      eq_refl).
  Qed.

  Lemma written_bytes_to_word (p : ptr) :
    type_ptr Tuint p **
    p |-> ucharR 1$m 4 **
    p .[Tuchar ! 1] |-> ucharR 1$m 3 **
    p .[Tuchar ! 2] |-> ucharR 1$m 2 **
    p .[Tuchar ! 3] |-> ucharR 1$m 1 **
    p .[Tuchar ! 4] |-> arrayR Tuchar
      (fun b : N => primR Tuchar 1$m (Vn b)) []
    |-- p |-> uintR 1$m 16909060.
  Proof using MODd.
    rewrite (word_bytes 1$m 16909060 [4%N;3%N;2%N;1%N]
      ltac:(split;
        [ repeat (apply List.Forall_cons; [rewrite -has_int_type; done | ]);
          apply List.Forall_nil
        | rewrite z_to_bytes._Z_from_bytes_eq; reflexivity ]) eq_refl).
    rewrite !arrayR_cons.
    go.
    normalize_ptrs.
    go.
  Qed.

  cpp.spec "scalar_byte_write()" as scalar_byte_write_spec with (
    \post [Vint 16909060] emp
  ).

  Lemma scalar_byte_write_ok : verify[source] scalar_byte_write_spec.
  Proof using MODd.
    verify_spec.
    go.
    rewrite zero_word_bytes.
    go using _at_arrayR_cons_F.
    normalize_ptrs.
    go.
    go using ([FWD] written_bytes_to_word x_addr).
  Qed.
End with_Sigma.

Set Printing Fully Qualified.
Print Assumptions scalar_byte_write_ok.
Unset Printing Fully Qualified.

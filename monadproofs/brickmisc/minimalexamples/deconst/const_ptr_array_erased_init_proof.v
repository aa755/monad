Set Default Goal Selector "!".


Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import monad.proofs.misc.

Import linearity.
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.

cpp.prog source prog cpp:{{
  namespace minimalexamples {
    using byte = unsigned char;

    void init_const_input_array(byte const *src, byte const **dst) {
      byte const *inputs[1];
      inputs[0] = src;
      *dst = inputs[0];
    }
  }
}}.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : source ⊧ CU}.

  cpp.spec
    "minimalexamples::init_const_input_array(unsigned char const*, unsigned char const**)"
    as init_const_input_array_spec with (
      \arg{srcp : ptr} "src" (Vptr srcp)
      \arg{dstp : ptr} "dst" (Vptr dstp)
      \pre{old : val}
        dstp |-> primR (Tptr Tuchar) 1$m old
      \post
        dstp |-> primR (Tptr Tuchar) 1$m (Vptr srcp)
    ).

  Example const_pointer_array_fails_upstream_fusion_side_condition :
    erase_qualifiers (Tptr (Qconst Tuchar)) <> Tptr (Qconst Tuchar).
  Proof.
    cbn.
    discriminate.
  Qed.

  Lemma init_const_input_array_proof :
    verify?[source] init_const_input_array_spec.
  Proof using MODd.
    verify_spec.
    go.
    replace (inputs_addr .[ Tptr Tuchar ! 0 ])
      with inputs_addr in *.
    2: {
      symmetry.
      apply offset_ptr_sub_0.
      rewrite size_of_pointer.
      eexists.
      reflexivity.
    }
    cbn.
    rewrite arrayR_singleton.
    go.
    normalize_ptrs.
    go.
    rewrite anyR_array'.
    cbn.
    rewrite arrayR_singleton.
    go.
  Qed.
End with_Sigma.

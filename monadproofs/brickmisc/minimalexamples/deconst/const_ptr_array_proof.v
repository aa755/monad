Set Default Goal Selector "!".

(*
  Minimal regression test for BRiCk issue #145.

  The C++ source is [const_ptr_array.cpp].  The function declares a local
  array whose element type is [unsigned char const *]:

<<
byte const *inputs[1];
inputs[0] = src;
>>

  Default-initializing that array should leave one uninitialized pointer object
  at the array's heap element address.  The upstream array initialization path
  now computes those addresses through the heap-erased type, so this file should
  prove without any local [o_sub_erase_qualifiers] or default-initialization
  axiom.

  The two facts below document the source/heap type distinction that originally
  triggered the issue.
*)

Require Import monad.brickmisc.minimalexamples.deconst.const_ptr_array_cpp.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.auto.cpp.tactics4.
Require Import monad.proofs.misc.

Import linearity.
#[local] Hint Resolve UNSAFE_read_prim_cancel : sl_opacity.

Example const_pointer_array_element_heap_type :
  erase_qualifiers (Tptr (Qconst Tuchar)) = Tptr Tuchar :=
  eq_refl.

Fail Example const_pointer_source_type_is_not_heap_type :
  erase_qualifiers (Tptr (Qconst Tuchar)) = Tptr (Qconst Tuchar) :=
  eq_refl.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : const_ptr_array_cpp.source ⊧ CU}.

  cpp.spec "minimalexamples::init_const_input_array(unsigned char const*, unsigned char const**)"
    as init_const_input_array_spec with (
      \arg{srcp : ptr} "src" (Vptr srcp)
      \arg{dstp : ptr} "dst" (Vptr dstp)
      \pre{old : val}
        dstp |-> primR (Tptr Tuchar) 1$m old
      \post
        dstp |-> primR (Tptr Tuchar) 1$m (Vptr srcp)
    ).

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

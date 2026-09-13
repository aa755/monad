Set Default Goal Selector "!".

(*
  Specs for Monad's generic big-endian integer conversion helpers.

  This file is deliberately separate from [u256_specs.v].  The conversion
  templates are needed only by the storage-key helpers; registering them in
  the broad uint256 spec environment makes unrelated large C++ proofs search
  these contracts at every call site.
*)

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.cpp.
Require Import monad.asts.state_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.u256_specs.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  (** The name gives call-site learning a stable head symbol; the definition is
      exactly the concrete 32-byte array consumed by [load_be]. *)
  Definition uint256_be_bytesR (q : cQp.t) (word : N) : Rep :=
    arrayR Tuchar
      (fun byte : val => primR Tuchar q byte)
      (bytes32_be_values word).

  #[global] Instance learn_uint256_be_bytesR :
    LearnEq2 uint256_be_bytesR := ltac:(solve_learnable).

  Lemma uint256_be_bytesR_unfold (p : ptr) q word :
    p |-> uint256_be_bytesR q word
    |--
    p |-> arrayR Tuchar
      (fun byte : val => primR Tuchar q byte)
      (bytes32_be_values word).
  Proof.
    reflexivity.
  Qed.

  Lemma uint256_be_bytesR_fold (p : ptr) q word :
    p |-> arrayR Tuchar
      (fun byte : val => primR Tuchar q byte)
      (bytes32_be_values word)
    |--
    p |-> uint256_be_bytesR q word.
  Proof.
    reflexivity.
  Qed.

  Definition uint256_be_bytesR_unfold_F p q word :=
    [FWD] (uint256_be_bytesR_unfold p q word).

  Definition uint256_be_bytesR_fold_F p q word :=
    [FWD] (uint256_be_bytesR_fold p q word).

  (** Load one 256-bit word from its 32-byte big-endian representation. *)
  cpp.spec
    "monad::load_be<monad::uint256_t, 32ul>(const unsigned char[32]&)"
    from state_cpp.source as load_be_uint256_bytes32_spec with (
      \arg{srcp : ptr} "src" (Vref srcp)
      \pre srcp |-> type_ptrR (Tarray Tuchar 32)
      \prepost{q word}
        srcp |-> uint256_be_bytesR q word
      \pre [| (word < uint256_word_modulus)%N |]
      \post{retp : ptr} [Vptr retp]
        retp |-> u256R 1 word
    ).

  (** Store one uint256 value as a [monad::bytes32_t] in big-endian order. *)
  cpp.spec
    "monad::store_be_as<monad::bytes32_t, monad::uint256_t>(monad::uint256_t)"
    from state_cpp.source as store_be_as_bytes32_uint256_spec with (
      \arg{xp : ptr} "x" (Vptr xp)
      \prepost{word} xp |-> u256R 1 word
      \post{retp : ptr} [Vptr retp]
        retp |-> bytes32R 1 word
    ).
End with_Sigma.

#[global] Hint Opaque
  uint256_be_bytesR
  load_be_uint256_bytes32_spec
  store_be_as_bytes32_uint256_spec : sl_opacity.

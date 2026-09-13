Set Default Goal Selector "!".

(*
  Specs for the RLP helpers used by storage-page encoding/decoding.

  The C++ functions are library calls, not part of the MIP-8 page-commit
  implementation.  Their observable behavior is connected to the pure Gallina
  encoding model from [storage_page_encoding.v].
*)

From Stdlib Require Import List ZArith.

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.lang.cpp.cpp.
Require Import monad.asts.storage_page_cpp.
Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.byte_string_specs.
Require Import monad.proofs.libspecs.outcome_specs.
Require Import monad.proofs.libspecs.outcome_status_code_specs.
Require Import monad.proofs.libspecs.result_model.
Require Import monad.proofs.libspecs.rlp_decode_error_model.
Require Import monad.proofs.libspecs.rlp_decode_error_specs.
Require Import monad.proofs.execproofs.mip8.storage_page_encoding.

Import ListNotations.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Definition bytes32_ty : type := "monad::bytes32_t"%cpp_type.

  Definition decode_string_result_name : name :=
    outcome_result_name
      byte_string_view_ty outcome_error_ty
      (outcome_status_code_throw_policy_ty
         byte_string_view_ty outcome_error_ty).

  #[global] Instance bytes32_outcome_object_value :
    OutcomeObjectValue bytes32_ty := {}.

  #[global] Instance byte_string_view_outcome_object_value :
    OutcomeObjectValue byte_string_view_ty := {}.

  #[global] Instance byte_string_view_move_residual :
    MoveResidualRep byte_string_view_ty (ptr * N) :=
    {| move_residualR :=
         fun value => ByteStringViewSpineR 1 value.1 value.2 |}.

  Definition decode_bytes32_result_name : name :=
    outcome_result_name
      bytes32_ty outcome_error_ty
      (outcome_status_code_throw_policy_ty bytes32_ty outcome_error_ty).

  Definition decode_bytes32_result_ty : type :=
    Tnamed decode_bytes32_result_name.

  #[global] Instance bytes32_move_residual :
    MoveResidualRep bytes32_ty N :=
    {| move_residualR := fun value => bytes32R 1 value |}.

  #[global] Instance decode_error_move_residual :
    MoveResidualRep decode_error_ty DecodeError.DecodeError.t :=
    {| move_residualR :=
         fun error => concepts.objR decode_error_ty 1 error |}.

  cpp.spec "monad::rlp::encode_bytes32_compact(const monad::bytes32_t&)"
    from storage_page_cpp.source as rlp_encode_bytes32_compact_spec
    with (
      \arg{bytep : ptr} "byte" (Vref bytep)
      \prepost{q word} bytep |-> bytes32R q word
      \post{retp : ptr} [Vptr retp]
        retp |-> ByteStringR 1$m (encode_slot_model word)
    ).

  cpp.spec "monad::rlp::decode_string(std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>&)"
    from storage_page_cpp.source as rlp_decode_string_spec
    with (
      \arg{encp : ptr} "enc" (Vref encp)
      \prepost{(q : Qp) (backing_base : ptr) (backing : list Z)}
        backing_base |-> array_sliceR Tuchar 0
          (Z.of_nat (length backing))
          (fun byte => ucharR (cQp.const q) byte) backing
      \pre{(bytes : list Z) (data : ptr)}
        encp |-> ByteStringViewSpineR 1 data
          (N.of_nat (length bytes))
      \pre [| byte_string_view_suffix
                backing_base backing data bytes |]
      \post{retp : ptr} [Vptr retp]
        Exists final_data : ptr,
          encp |-> ByteStringViewSpineR 1 final_data
            (N.of_nat
               (length (rlp_decode_string_final_view bytes)))
        ** [| byte_string_view_suffix
                  backing_base backing final_data
                  (rlp_decode_string_final_view bytes) |]
        ** match rlp_decode_string_result_model bytes with
           | Result.Ok (value, _) =>
               Exists value_data : ptr,
                 retp |-> ResultR byte_string_view_ty 1
                   (Result.Ok (value_data, N.of_nat (length value)))
               ** [| byte_string_view_window
                         backing_base backing value_data value |]
           | Result.Err error =>
               retp |-> ResultR byte_string_view_ty 1
                 (Result.Err error)
           end
    ).

  cpp.spec "monad::rlp::decode_bytes32_compact(std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>&)"
    from storage_page_cpp.source as rlp_decode_bytes32_compact_spec
    with (
      \arg{encp : ptr} "enc" (Vref encp)
      \prepost{(q : Qp) (backing_base : ptr) (backing : list Z)}
        backing_base |-> array_sliceR Tuchar 0
          (Z.of_nat (length backing))
          (fun byte => ucharR (cQp.const q) byte) backing
      \pre{(bytes : list Z) (data : ptr)}
        encp |-> ByteStringViewSpineR 1 data
          (N.of_nat (length bytes))
      \pre [| byte_string_view_suffix
                backing_base backing data bytes |]
      \post{retp : ptr} [Vptr retp]
        Exists final_data : ptr,
          encp |-> ByteStringViewSpineR 1 final_data
            (N.of_nat
               (length (rlp_decode_string_final_view bytes)))
        ** [| byte_string_view_suffix
                  backing_base backing final_data
                  (rlp_decode_string_final_view bytes) |]
        ** match rlp_decode_bytes32_compact_result_model bytes with
           | Result.Ok (value, _) =>
               retp |-> ResultR bytes32_ty 1 (Result.Ok value)
           | Result.Err error =>
               retp |-> ResultR bytes32_ty 1 (Result.Err error)
           end
    ).

  cpp.spec "monad::to_bytes(std::basic_string_view<unsigned char, evmc::byte_traits<unsigned char>>)"
    from storage_page_cpp.source as to_bytes_string_view_spec
    with (
      \arg{viewp : ptr} "" (Vptr viewp)
      \prepost{(qv : Qp) (data : ptr) (bytes : list Z)}
        viewp |-> ByteStringViewSpineR qv data
          (N.of_nat (length bytes))
      \prepost{(qb : Qp) (backing_base : ptr) (backing : list Z)}
        backing_base |-> array_sliceR Tuchar 0
          (Z.of_nat (length backing))
          (fun byte => ucharR (cQp.const qb) byte) backing
      \pre [| byte_string_view_window
                backing_base backing data bytes |]
      \pre [| length bytes <= 32 |]
      \post{retp : ptr} [Vptr retp]
        retp |-> bytes32R 1 (word_of_compact_payload bytes)
    ).

End with_Sigma.

Set Default Goal Selector "!".

(** The logical type of failed Monad RLP decodes.  The C++ enum also contains a
    [Success] enumerator, but it cannot inhabit the error alternative of
    [Result<T>].  Omitting it here makes that invariant structural rather than
    an uninhabited separation-logic side condition.  This pure model contains
    no generated C++ AST, representation predicate, or System Error 2
    machinery; [rlp_decode_error_specs.v] maps these failures to the
    corresponding C++ enum values. *)

Module DecodeError.
  Module DecodeError.
    Inductive t : Type :=
    | TypeUnexpected
    | Overflow
    | InputTooLong
    | InputTooShort
    | ArrayLengthUnexpected
    | InvalidTxnType
    | LeadingZero
    | PathTooShort
    | PathTooLong
    | NonCanonical.
  End DecodeError.
End DecodeError.

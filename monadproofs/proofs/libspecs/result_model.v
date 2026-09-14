Set Default Goal Selector "!".

(** A small, C++-independent model of a computation that returns either a
    value or a typed error.  Library representation predicates such as
    [ResultR] connect this type to a concrete C++ result implementation. *)
Module Result.
  Inductive t (A E : Type) : Type :=
  | Ok (value : A) : t A E
  | Err (error : E) : t A E.

  Arguments Ok {A E} value.
  Arguments Err {A E} error.

  Definition to_option {A E : Type} (result : t A E) : option A :=
    match result with
    | Ok value => Some value
    | Err _ => None
    end.
End Result.

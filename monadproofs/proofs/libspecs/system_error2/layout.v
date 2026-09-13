Set Default Goal Selector "!".

(**
  C++ names and layout facts for the System Error 2 headers used by Monad.

  The workspace currently preprocesses Boost 1.90.0
  ([BOOST_VERSION = 109000], Debian package [libboost1.90-dev
  1.90.0-6ubuntu1]).  cpp2v reads the single-level headers below:

  - [boost/outcome/experimental/status-code/status_code_domain.hpp]
  - [boost/outcome/experimental/status-code/status_code.hpp]
  - [boost/outcome/experimental/status-code/errored_status_code.hpp]

  In [storage_page_cpp.v], the erased error is 16 bytes with alignment 8.
  Its inheritance path is

  {[
  errored_status_code<erased<long>>
    -> status_code<erased<long>>
    -> mixins::mixin<status_code_storage<erased<long>>, erased<long>>
    -> detail::status_code_storage<erased<long>>
    -> status_code<void>
  ]}

  Only [status_code<void>] and [status_code_storage] contribute fields:
  the domain pointer is at byte offset 0 and the erased [long] is at byte
  offset 8.  The names below reproduce those structured AST names without
  depending on cpp2v's generated local aliases.
*)

Require Import skylabs.lang.cpp.cpp.

Definition system_error2_boost_version : N := 109000%N.

Definition status_code_domain_name : name :=
  "system_error2::status_code_domain"%cpp_name.

Definition status_code_domain_ty : type :=
  Tnamed status_code_domain_name.

Definition erased_long_name : name :=
  Ninst "system_error2::detail::erased"%cpp_name [Atype Tlong].

Definition erased_long_ty : type :=
  Tnamed erased_long_name.

Definition status_code_void_name : name :=
  Ninst "system_error2::status_code"%cpp_name [Atype Tvoid].

Definition status_code_void_ty : type :=
  Tnamed status_code_void_name.

Definition erased_status_storage_name : name :=
  Ninst "system_error2::detail::status_code_storage"%cpp_name
    [Atype erased_long_ty].

Definition erased_status_storage_ty : type :=
  Tnamed erased_status_storage_name.

Definition erased_status_mixin_name : name :=
  Ninst "system_error2::mixins::mixin"%cpp_name
    [Atype erased_status_storage_ty; Atype erased_long_ty].

Definition erased_status_mixin_ty : type :=
  Tnamed erased_status_mixin_name.

Definition erased_status_code_name : name :=
  Ninst "system_error2::status_code"%cpp_name [Atype erased_long_ty].

Definition erased_status_code_ty : type :=
  Tnamed erased_status_code_name.

Definition erased_errored_status_code_name : name :=
  Ninst "system_error2::errored_status_code"%cpp_name
    [Atype erased_long_ty].

Definition erased_errored_status_code_ty : type :=
  Tnamed erased_errored_status_code_name.

Definition status_code_domain_field : name :=
  "system_error2::status_code<void>::_domain"%cpp_field.

Definition erased_status_value_field : name :=
  "system_error2::detail::status_code_storage<system_error2::detail::erased<long>>::_value"%cpp_field.

Definition status_domain_id_field : name :=
  "system_error2::status_code_domain::_id"%cpp_field.

(** The concrete quick-enum type is parameterized by the enum type. *)
Definition quick_enum_domain_name (enum_ty : type) : name :=
  Ninst "system_error2::_quick_status_code_from_enum_domain"%cpp_name
    [Atype enum_ty].

Definition quick_enum_domain_ty (enum_ty : type) : type :=
  Tnamed (quick_enum_domain_name enum_ty).

Definition quick_enum_status_code_name (enum_ty : type) : name :=
  Ninst "system_error2::status_code"%cpp_name
    [Atype (quick_enum_domain_ty enum_ty)].

Definition quick_enum_status_code_ty (enum_ty : type) : type :=
  Tnamed (quick_enum_status_code_name enum_ty).

(** Header-level variable template holding the process-wide quick-enum domain. *)
Definition quick_enum_domain_global_name (enum_ty : type) : name :=
  Ninst "system_error2::quick_status_code_from_enum_domain"%cpp_name
    [Atype enum_ty].

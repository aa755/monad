Set Default Goal Selector "!".

(* Integer operations used by storage-page key construction. *)
Require Import monad.proofs.exec_specs.
Require Import monad.asts.storage_page_cpp.
Require Import monad.proofs.libspecs.const_specs.
Require Import skylabs.auto.cpp.proof.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Definition uint256_word_modulus : N := N.pow 2 256.

  Opaque u256R u256_words_arrayR u256_word_cellsR.

  cpp.spec "monad::uint256_t::uint256_t<unsigned long>(unsigned long)"
    from storage_page_cpp.source as uint256constr with (
      fun this : ptr =>
        \arg{n : N} "v" (Vn n)
        \post this |-> u256R 1 n
    ).

  cpp.spec
    "monad::uint256_t::uint256_t<unsigned char>(unsigned char)"
    from storage_page_cpp.source as uint256_uchar_ctor_spec with (
      fun this : ptr =>
        \arg{n : Z} "v" (Vint n)
        \pre [| 0 <= n < 256 |]%Z
        \post this |-> u256R 1 (Z.to_N n)
    ).

  cpp.spec "monad::uint256_t::uint256_t(const monad::uint256_t&)"
    from storage_page_cpp.source as uint256_copy_ctor_spec with (
      fun this : ptr =>
        \arg{otherp : ptr} "other" (Vref otherp)
        \prepost{qv v} otherp |-> u256R qv v
        \post this |-> u256R 1 v
    ).

  cpp.spec "monad::uint256_t::~uint256_t()"
    from storage_page_cpp.source as uint256dtor with (
      fun this : ptr =>
        \pre{w} this |-> u256R 1 w
        \post emp
    ).

  cpp.spec "monad::operator|(const monad::uint256_t&, const monad::uint256_t&)"
    from storage_page_cpp.source as u256_or_spec with (
      \arg{xp : ptr} "x" (Vref xp)
      \arg{yp : ptr} "y" (Vref yp)
      \pre{qx qy xword yword}
        xp |-> u256R qx xword
        ** yp |-> u256R qy yword
      \post{retp : ptr} [Vptr retp]
        xp |-> u256R qx xword
        ** yp |-> u256R qy yword
        ** retp |-> u256R 1 (N.lor xword yword)
    ).

  cpp.spec
    ("monad::operator<<(const monad::uint256_t&, unsigned long)"
       .<< Atype Tulong >>)
    from storage_page_cpp.source as u256_shl_ulong_spec with (
      \arg{xp : ptr} "x" (Vref xp)
      \arg{shift : N} "shift0" (Vn shift)
      \pre{q word} xp |-> u256R q word
      \post{retp : ptr} [Vptr retp]
        xp |-> u256R q word
        ** retp |-> u256R 1
             (N.modulo (N.shiftl word shift) uint256_word_modulus)
    ).

  cpp.spec "monad::operator>>(const monad::uint256_t&, const monad::uint256_t&)"
    from storage_page_cpp.source as u256_shr_spec with (
      \arg{xp : ptr} "x" (Vref xp)
      \arg{shiftp : ptr} "shift" (Vref shiftp)
      \pre{qx qshift word shift}
        xp |-> u256R qx word
        ** shiftp |-> u256R qshift shift
      \post{retp : ptr} [Vptr retp]
        xp |-> u256R qx word
        ** shiftp |-> u256R qshift shift
        ** retp |-> u256R 1 (N.shiftr word shift)
    ).
End with_Sigma.

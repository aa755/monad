Require Import monad.proofs.exec_specs.
Require Import monad.asts.ext.
Require Import monad.asts.reserve_balance_cpp.
Require Import monad.asts.state_cpp.
Require Import monad.proofs.libspecs.const_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import skylabs.auto.cpp.hints.const.
Require Import skylabs.auto.cpp.proof.
Require Import Lens.Lens.

Set Default Goal Selector "!".

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}.
  Context {hf: fracG () _Σ}.
  Context {MODd : ext.source ⊧ CU}.

  Definition uint256_word_modulus : N := N.pow 2 256.
  Definition uint64_word_modulus : Z := 2 ^ 64.

  Lemma reserve_balance_optional_u256R_const :
    const.CONST1 reserve_balance_cpp.source
      (optional_specs.trivial_optional_name u256t)
      (optional_specs.optionR u256t u256R).
  Proof.
    intros a p from to.
    eapply const.transport'.
    { intros q. apply optional_specs.optionR_layout. }
    Transparent optional_specs.trivial_optional_baseR
      optional_specs.trivial_optional_payloadR
      optional_specs.trivial_optional_payload_baseR
      optional_specs.trivial_optional_storageR.
    unfold optional_specs.trivial_optional_baseR,
      optional_specs.trivial_optional_payloadR,
      optional_specs.trivial_optional_payload_baseR,
      optional_specs.trivial_optional_storageR.
    destruct a.
    { go using const_specs.u256R_const_C. }
    { go. }
  Qed.

  Opaque optional_specs.optionR
    optional_specs.trivial_optional_baseR
    optional_specs.trivial_optional_payloadR
    optional_specs.trivial_optional_payload_baseR
    optional_specs.trivial_optional_storageR.

  Definition reserve_balance_optional_u256R_const_C :=
    [CANCEL] reserve_balance_optional_u256R_const.

  Definition optional_u256_ctor_rv_spec : mpred :=
    let opt := optional_specs.trivial_optional_name u256t in
    specify
      {| info_name :=
           Ninst (Nscoped opt (Nctor [Trv_ref u256t])) [Atype u256t];
         info_type := tCtor opt [Trv_ref u256t] |}
      (fun this =>
        \arg{valuep : ptr} "__t" (Vref valuep)
        \prepost{(qv : Qp) (value : N)}
          valuep |-> u256R (cQp.mut qv) value
        \post
          this |-> optional_specs.optionR
            u256t u256R 1$m (Some value)).

  Definition optional_u256_ctor_const_rv_spec : mpred :=
    let opt := optional_specs.trivial_optional_name u256t in
    specify
      {| info_name :=
           Ninst (Nscoped opt (Nctor [Trv_ref (Tconst u256t)]))
             [Atype (Tconst u256t)];
         info_type := tCtor opt [Trv_ref (Tconst u256t)] |}
      (fun this =>
        \arg{valuep : ptr} "__t" (Vref valuep)
        \prepost{(qv : Qp) (value : N)}
          valuep |-> u256R (cQp.const qv) value
        \post
          this |-> optional_specs.optionR
            u256t u256R 1$m (Some value)).

  Definition optional_u256_ctor_nullopt_spec : mpred :=
    specify.template.ctor (optional_specs.trivial_optional_name u256t)
      ["std::nullopt_t"%cpp_type] $
      fun this =>
        \arg{tagp : ptr} "__t" (Vref tagp)
        \post
          this |-> optional_specs.optionR
            u256t u256R 1$m None.

  Definition optional_u256_has_value_spec : mpred :=
    specify.template.method (optional_specs.trivial_optional_name u256t)
      "has_value" function_qualifiers.Nc "bool" [] $
      \this this
      \prepost{(value : option N) (q : cQp.t)}
        this |-> optional_specs.optionR u256t u256R q value
      \post [Vbool (bool_decide (is_Some value))] emp.

  Definition optional_u256_value_const_spec : mpred :=
    specify.template.method (optional_specs.trivial_optional_name u256t)
      "value" function_qualifiers.Ncl (Tref (Tconst u256t)) [] $
      \this this
      \prepost{(value : N) (q : cQp.t)}
        this |-> optional_specs.optionR
          u256t u256R q (Some value)
      \post
        [Vptr (optional_specs.trivial_optional_value_ptr u256t this)] emp.

  Definition optional_u256_dtor_spec : mpred :=
    specify.template.dtor (optional_specs.trivial_optional_name u256t) $
      \this this
      \pre{value : option N}
        this |-> optional_specs.optionR
          u256t u256R 1$m value
      \post emp.

  Opaque u256R u256_words_arrayR u256_word_cellsR.

  cpp.spec "monad::uint256_t::uint256_t<int>(int)"
    from state_cpp.source as uint256_int_ctor_spec with (
      fun this : ptr =>
        \arg{n : Z} "v" (Vint n)
        \pre [| (- (2 ^ 31) <= n < 2 ^ 31)%Z |]
        \post this |-> u256R 1 (Z.to_N (n mod uint64_word_modulus)%Z)
    ).

  cpp.spec "monad::uint256_t::uint256_t<unsigned long>(unsigned long)"
    from state_cpp.source as uint256constr with (
      fun this : ptr =>
        \arg{n : N} "v" (Vn n)
        \post this |-> u256R 1 n
    ).

  cpp.spec
    "monad::uint256_t::uint256_t<unsigned char>(unsigned char)"
    from state_cpp.source as uint256_uchar_ctor_spec with (
      fun this : ptr =>
        \arg{n : Z} "v" (Vint n)
        \pre [| 0 <= n < 256 |]%Z
        \post this |-> u256R 1 (Z.to_N n)
    ).

  cpp.spec "monad::uint256_t::uint256_t(const monad::uint256_t&)"
    from state_cpp.source as uint256_copy_ctor_spec with (
      fun this : ptr =>
        \arg{otherp : ptr} "other" (Vref otherp)
        \prepost{qv v} otherp |-> u256R qv v
        \post this |-> u256R 1 v
    ).

  cpp.spec "monad::uint256_t::~uint256_t()"
    from state_cpp.source as uint256dtor with (
      fun this : ptr =>
        \pre{w} this |-> u256R 1 w
        \post emp
    ).

  cpp.spec "monad::uint256_t::operator=(const monad::uint256_t&)"
    from state_cpp.source as u256_assign_spec with (
      fun this : ptr =>
        \arg{yp : ptr} "y" (Vref yp)
        \pre{(qy : cQp.t) (xv yv : N)}
          this |-> u256R 1$m xv
          ** yp |-> u256R qy yv
        \post[Vref this]
          this |-> u256R 1$m yv
          ** yp |-> u256R qy yv
    ).

  (* The defaulted move assignment only reads the scalar source words. *)
  cpp.spec "monad::uint256_t::operator=(monad::uint256_t&&)"
    from state_cpp.source as u256_move_assign_spec with (
      fun this : ptr =>
        \arg{yp : ptr} "y" (Vref yp)
        \pre{(qy : cQp.t) (xv yv : N)}
          this |-> u256R 1$m xv
          ** yp |-> u256R qy yv
        \post[Vref this]
          this |-> u256R 1$m yv
          ** yp |-> u256R qy yv
    ).

  cpp.spec "monad::operator+(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_plus_spec with (
      \arg{ap : ptr} "lhs" (Vref ap)
      \arg{bp : ptr} "rhs" (Vref bp)
      \pre{(qa qb : cQp.t) (av bv : N)}
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
      \post{retp : ptr} [Vptr retp]
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
        ** retp |-> u256R 1
             (N.modulo (av + bv)%N uint256_word_modulus)
    ).

  cpp.spec "monad::operator-(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_minus_spec with (
      \arg{ap : ptr} "lhs" (Vref ap)
      \arg{bp : ptr} "rhs" (Vref bp)
      \pre{(qa qb : cQp.t) (av bv : N)}
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
      \post{retp : ptr} [Vptr retp]
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
        ** retp |-> u256R 1
             (Z.to_N ((Z.of_N av - Z.of_N bv) mod 2 ^ 256)%Z)
    ).

  cpp.spec "monad::operator*(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_mul_spec with (
      \arg{ap : ptr} "lhs" (Vref ap)
      \arg{bp : ptr} "rhs" (Vref bp)
      \pre{(qa qb : cQp.t) (av bv : N)}
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
      \post{retp : ptr} [Vptr retp]
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
        ** retp |-> u256R 1
             (N.modulo (av * bv)%N uint256_word_modulus)
    ).

  cpp.spec "monad::operator/(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_div_spec with (
      \arg{ap : ptr} "x" (Vref ap)
      \arg{bp : ptr} "y" (Vref bp)
      \pre{(qa qb : cQp.t) (av bv : N)}
        [| bv <> 0%N |]
        ** ap |-> u256R qa av
        ** bp |-> u256R qb bv
      \post{retp : ptr} [Vptr retp]
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
        ** retp |-> u256R 1 (N.div av bv)
    ).

  cpp.spec "monad::operator%(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_mod_spec with (
      \arg{ap : ptr} "x" (Vref ap)
      \arg{bp : ptr} "y" (Vref bp)
      \pre{(qa qb : cQp.t) (av bv : N)}
        [| bv <> 0%N |]
        ** ap |-> u256R qa av
        ** bp |-> u256R qb bv
      \post{retp : ptr} [Vptr retp]
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
        ** retp |-> u256R 1 (N.modulo av bv)
    ).

  cpp.spec "monad::operator==(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_eq_spec with (
      \arg{ap : ptr} "x" (Vref ap)
      \arg{bp : ptr} "y" (Vref bp)
      \pre{(qa qb : cQp.t) (av bv : N)}
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
      \post[Vbool (bool_decide (av = bv))]
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
    ).

  cpp.spec "monad::operator<(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_lt_spec with (
      \arg{ap : ptr} "lhs" (Vref ap)
      \arg{bp : ptr} "rhs" (Vref bp)
      \pre{(qa qb : cQp.t) (av bv : N)}
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
      \post[Vbool (bool_decide (av < bv)%N)]
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
    ).

  cpp.spec "monad::operator<=(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_le_spec with (
      \arg{ap : ptr} "lhs" (Vref ap)
      \arg{bp : ptr} "rhs" (Vref bp)
      \pre{(qa qb : cQp.t) (av bv : N)}
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
      \post[Vbool (bool_decide (av <= bv)%N)]
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
    ).

  cpp.spec "monad::operator>(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_gt_spec with (
      \arg{ap : ptr} "lhs" (Vref ap)
      \arg{bp : ptr} "rhs" (Vref bp)
      \pre{(qa qb : cQp.t) (av bv : N)}
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
      \post[Vbool (bool_decide (bv < av)%N)]
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
    ).

  cpp.spec "monad::operator>=(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_ge_spec with (
      \arg{ap : ptr} "lhs" (Vref ap)
      \arg{bp : ptr} "rhs" (Vref bp)
      \pre{(qa qb : cQp.t) (av bv : N)}
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
      \post[Vbool (bool_decide (bv <= av)%N)]
        ap |-> u256R qa av
        ** bp |-> u256R qb bv
    ).

  cpp.spec "monad::operator&(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_and_spec with (
      \arg{xp : ptr} "x" (Vref xp)
      \arg{yp : ptr} "y" (Vref yp)
      \pre{qx qy xword yword}
        xp |-> u256R qx xword
        ** yp |-> u256R qy yword
      \post{retp : ptr} [Vptr retp]
        xp |-> u256R qx xword
        ** yp |-> u256R qy yword
        ** retp |-> u256R 1 (N.land xword yword)
    ).

  cpp.spec "monad::operator|(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_or_spec with (
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

  cpp.spec "monad::operator^(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_xor_spec with (
      \arg{xp : ptr} "x" (Vref xp)
      \arg{yp : ptr} "y" (Vref yp)
      \pre{qx qy xword yword}
        xp |-> u256R qx xword
        ** yp |-> u256R qy yword
      \post{retp : ptr} [Vptr retp]
        xp |-> u256R qx xword
        ** yp |-> u256R qy yword
        ** retp |-> u256R 1 (N.lxor xword yword)
    ).

  cpp.spec "monad::uint256_t::operator-() const"
    from state_cpp.source as u256_unary_minus_spec with (
      fun this : ptr =>
        \pre{q word} this |-> u256R q word
        \post{retp : ptr} [Vptr retp]
          this |-> u256R q word
          ** retp |-> u256R 1
               (Z.to_N ((0 - Z.of_N word) mod 2 ^ 256)%Z)
    ).

  cpp.spec "monad::uint256_t::operator~() const"
    from state_cpp.source as u256_bitwise_not_spec with (
      fun this : ptr =>
        \pre{q word} this |-> u256R q word
        \post{retp : ptr} [Vptr retp]
          this |-> u256R q word
          ** retp |-> u256R 1 (N.lxor word (uint256_word_modulus - 1))
    ).

  cpp.spec
    ("monad::operator<<(const monad::uint256_t&, unsigned long)"
       .<< Atype Tulong >>)
    from state_cpp.source as u256_shl_ulong_spec with (
      \arg{xp : ptr} "x" (Vref xp)
      \arg{shift : N} "shift0" (Vn shift)
      \pre{q word} xp |-> u256R q word
      \post{retp : ptr} [Vptr retp]
        xp |-> u256R q word
        ** retp |-> u256R 1
             (N.modulo (N.shiftl word shift) uint256_word_modulus)
    ).

  cpp.spec
    ("monad::operator<<(const monad::uint256_t&, int)" .<< Atype Tint >>)
    from state_cpp.source as u256_shl_int_spec with (
      \arg{xp : ptr} "x" (Vref xp)
      \arg{shift : Z} "shift0" (Vint shift)
      \pre{q word}
        [| (- (2 ^ 31) <= shift < 2 ^ 31)%Z |]
        ** xp |-> u256R q word
      \post{retp : ptr} [Vptr retp]
        xp |-> u256R q word
        ** retp |-> u256R 1
             (if bool_decide (shift < 0)%Z
              then 0%N
              else N.modulo (N.shiftl word (Z.to_N shift))
                     uint256_word_modulus)
    ).

  cpp.spec "monad::operator<<(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_shl_spec with (
      \arg{xp : ptr} "x" (Vref xp)
      \arg{shiftp : ptr} "shift" (Vref shiftp)
      \pre{qx qshift word shift}
        xp |-> u256R qx word
        ** shiftp |-> u256R qshift shift
      \post{retp : ptr} [Vptr retp]
        xp |-> u256R qx word
        ** shiftp |-> u256R qshift shift
        ** retp |-> u256R 1
             (N.modulo (N.shiftl word shift) uint256_word_modulus)
    ).

  cpp.spec "monad::operator>>(const monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_shr_spec with (
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

  cpp.spec "monad::uint256_t::operator<<=(const monad::uint256_t&)"
    from state_cpp.source as u256_shl_assign_spec with (
      fun this : ptr =>
        \arg{shiftp : ptr} "shift0" (Vref shiftp)
        \pre{qshift word shift}
          this |-> u256R 1$m word
          ** shiftp |-> u256R qshift shift
        \post[Vref this]
          this |-> u256R 1$m
            (N.modulo (N.shiftl word shift) uint256_word_modulus)
          ** shiftp |-> u256R qshift shift
    ).

  cpp.spec "monad::uint256_t::operator>>=(const monad::uint256_t&)"
    from state_cpp.source as u256_shr_assign_spec with (
      fun this : ptr =>
        \arg{shiftp : ptr} "shift" (Vref shiftp)
        \pre{qshift word shift}
          this |-> u256R 1$m word
          ** shiftp |-> u256R qshift shift
        \post[Vref this]
          this |-> u256R 1$m (N.shiftr word shift)
          ** shiftp |-> u256R qshift shift
    ).

  cpp.spec "monad::operator+=(monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_add_assign_spec with (
      \arg{lhsp : ptr} "lhs" (Vref lhsp)
      \arg{rhsp : ptr} "rhs" (Vref rhsp)
      \pre{(qrhs : cQp.t) (lhs rhs : N)}
        lhsp |-> u256R 1$m lhs
        ** rhsp |-> u256R qrhs rhs
      \post[Vref lhsp]
        lhsp |-> u256R 1$m
          (N.modulo (lhs + rhs)%N uint256_word_modulus)
        ** rhsp |-> u256R qrhs rhs
    ).

  cpp.spec "monad::operator-=(monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_sub_assign_spec with (
      \arg{lhsp : ptr} "lhs" (Vref lhsp)
      \arg{rhsp : ptr} "rhs" (Vref rhsp)
      \pre{(qrhs : cQp.t) (lhs rhs : N)}
        lhsp |-> u256R 1$m lhs
        ** rhsp |-> u256R qrhs rhs
      \post[Vref lhsp]
        lhsp |-> u256R 1$m
          (Z.to_N ((Z.of_N lhs - Z.of_N rhs) mod 2 ^ 256)%Z)
        ** rhsp |-> u256R qrhs rhs
    ).

  cpp.spec "monad::operator*=(monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_mul_assign_spec with (
      \arg{lhsp : ptr} "lhs" (Vref lhsp)
      \arg{rhsp : ptr} "rhs" (Vref rhsp)
      \pre{(qrhs : cQp.t) (lhs rhs : N)}
        lhsp |-> u256R 1$m lhs
        ** rhsp |-> u256R qrhs rhs
      \post[Vref lhsp]
        lhsp |-> u256R 1$m
          (N.modulo (lhs * rhs)%N uint256_word_modulus)
        ** rhsp |-> u256R qrhs rhs
    ).

  cpp.spec "monad::operator/=(monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_div_assign_spec with (
      \arg{lhsp : ptr} "lhs" (Vref lhsp)
      \arg{rhsp : ptr} "rhs" (Vref rhsp)
      \pre{(qrhs : cQp.t) (lhs rhs : N)}
        [| rhs <> 0%N |]
        ** lhsp |-> u256R 1$m lhs
        ** rhsp |-> u256R qrhs rhs
      \post[Vref lhsp]
        lhsp |-> u256R 1$m (N.div lhs rhs)
        ** rhsp |-> u256R qrhs rhs
    ).

  cpp.spec "monad::operator%=(monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_mod_assign_spec with (
      \arg{lhsp : ptr} "lhs" (Vref lhsp)
      \arg{rhsp : ptr} "rhs" (Vref rhsp)
      \pre{(qrhs : cQp.t) (lhs rhs : N)}
        [| rhs <> 0%N |]
        ** lhsp |-> u256R 1$m lhs
        ** rhsp |-> u256R qrhs rhs
      \post[Vref lhsp]
        lhsp |-> u256R 1$m (N.modulo lhs rhs)
        ** rhsp |-> u256R qrhs rhs
    ).

  cpp.spec "monad::operator^=(monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_xor_assign_spec with (
      \arg{lhsp : ptr} "lhs" (Vref lhsp)
      \arg{rhsp : ptr} "rhs" (Vref rhsp)
      \pre{(qrhs : cQp.t) (lhs rhs : N)}
        lhsp |-> u256R 1$m lhs
        ** rhsp |-> u256R qrhs rhs
      \post[Vref lhsp]
        lhsp |-> u256R 1$m (N.lxor lhs rhs)
        ** rhsp |-> u256R qrhs rhs
    ).

  cpp.spec "monad::operator|=(monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_or_assign_spec with (
      \arg{lhsp : ptr} "lhs" (Vref lhsp)
      \arg{rhsp : ptr} "rhs" (Vref rhsp)
      \pre{(qrhs : cQp.t) (lhs rhs : N)}
        lhsp |-> u256R 1$m lhs
        ** rhsp |-> u256R qrhs rhs
      \post[Vref lhsp]
        lhsp |-> u256R 1$m (N.lor lhs rhs)
        ** rhsp |-> u256R qrhs rhs
    ).

  cpp.spec "monad::operator&=(monad::uint256_t&, const monad::uint256_t&)"
    from state_cpp.source as u256_and_assign_spec with (
      \arg{lhsp : ptr} "lhs" (Vref lhsp)
      \arg{rhsp : ptr} "rhs" (Vref rhsp)
      \pre{(qrhs : cQp.t) (lhs rhs : N)}
        lhsp |-> u256R 1$m lhs
        ** rhsp |-> u256R qrhs rhs
      \post[Vref lhsp]
        lhsp |-> u256R 1$m (N.land lhs rhs)
        ** rhsp |-> u256R qrhs rhs
    ).

  Definition SpecFor_optional_u256_ctor_rv :=
    RegisterSpec optional_u256_ctor_rv_spec.
  #[global] Existing Instance SpecFor_optional_u256_ctor_rv.

  Definition SpecFor_optional_u256_ctor_const_rv :=
    RegisterSpec optional_u256_ctor_const_rv_spec.
  #[global] Existing Instance SpecFor_optional_u256_ctor_const_rv.

  Definition SpecFor_optional_u256_ctor_nullopt :=
    RegisterSpec optional_u256_ctor_nullopt_spec.
  #[global] Existing Instance SpecFor_optional_u256_ctor_nullopt.

  Definition SpecFor_optional_u256_has_value :=
    RegisterSpec optional_u256_has_value_spec.
  #[global] Existing Instance SpecFor_optional_u256_has_value.

  Definition SpecFor_optional_u256_value_const :=
    RegisterSpec optional_u256_value_const_spec.
  #[global] Existing Instance SpecFor_optional_u256_value_const.

  Definition SpecFor_optional_u256_dtor :=
    RegisterSpec optional_u256_dtor_spec.
  #[global] Existing Instance SpecFor_optional_u256_dtor.

End with_Sigma.

#[global] Hint Resolve reserve_balance_optional_u256R_const_C : sl_opacity.
#[global] Hint Opaque uint256_int_ctor_spec : sl_opacity.

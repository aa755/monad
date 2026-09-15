Set Default Goal Selector "!".

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.cpp.spec.concepts.
Require Import skylabs.lang.cpp.cpp.
Require Import monad.proofs.misc.
Require Import monad.asts.storage_page_cpp.
Require Export skylabs.auto.cpp.spec.

Import linearity.
Import cQp_compat.
#[local] Open Scope Z_scope.
Set Warnings "+sl-impossible-patterns".

Notation u256t := ("monad::uint256_t"%cpp_type).

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)


  Local Definition u256_words_array_name : name :=
    Ninst (Nscoped (Nglobal (Nid "std")) (Nid "array"))
      [Atype Tulong; Avalue (Eint 4 Tulong)].

  Definition u256_words (n : N) : list N :=
    [N.land n 18446744073709551615;
     N.land (N.shiftr n 64) 18446744073709551615;
     N.land (N.shiftr n 128) 18446744073709551615;
     N.land (N.shiftr n 192) 18446744073709551615].

  Definition u256_word_cellsR (q : cQp.t) (n : N) : Rep :=
    type_ptrR (Tarray Tulong 4)
    ** arrayR Tulong
         (fun word => primR Tulong q (Vn word)) (u256_words n).

  Definition u256_words_arrayR (q : cQp.t) (n : N) : Rep :=
    _field (Field u256_words_array_name (field_name.Id "_M_elems"))
      |-> u256_word_cellsR q n
    ** structR u256_words_array_name q.

  Definition u256R (q : cQp.t) (n : N) : Rep :=
    _field "monad::uint256_t::words_" |-> u256_words_arrayR q n
    ** structR "monad::uint256_t"%cpp_name q
    ** pureR [| (n < 2 ^ 256)%N |].

  #[global] Instance u256R_cfractional : CFractional1 u256R.
  Proof.
    intros n.
    unfold u256R, u256_words_arrayR, u256_word_cellsR.
    apply _.
  Qed.

  #[global] Instance u256R_as_cfractional : AsCFractional1 u256R.
  Proof.
    solve_as_cfrac.
  Qed.

  #[global] Instance observe_u256R_type (q : cQp.t) (n : N) :
    Observe (type_ptrR u256t) (u256R q n).
  Proof.
    unfold u256R.
    apply _.
  Qed.

  #[global] Instance observe_u256R_range (q : cQp.t) (n : N) :
    Observe (pureR [| (n < 2 ^ 256)%N |]) (u256R q n).
  Proof.
    unfold u256R.
    apply _.
  Qed.

  Fixpoint bytes32_be_values_from (len : nat) (z : N) : list val :=
    match len with
    | O => []
    | S len' =>
        Vint (Z.of_N (N.land (N.shiftr z (8 * N.of_nat len')) 255))
        :: bytes32_be_values_from len' z
    end.

  Definition bytes32_be_values (z : N) : list val :=
    bytes32_be_values_from 32 z.

  Definition evmc_bytes32_bytesR (q : cQp.t) (z : N) : Rep :=
    type_ptrR (Tarray Tuchar 32)
    ** arrayR Tuchar (primR Tuchar q) (bytes32_be_values z).

  Definition evmc_bytes32_wordR (q : cQp.t) (z : N) : Rep :=
    _field "evmc_bytes32::bytes" |-> evmc_bytes32_bytesR q z
    ** structR "evmc_bytes32"%cpp_name q.

  Definition bytes32R (q : cQp.t) (z : N) : Rep :=
    structR "monad::bytes32_t"%cpp_name q
    ** _base "monad::bytes32_t"%cpp_name "evmc_bytes32"%cpp_name
       |-> evmc_bytes32_wordR q z
    ** pureR [| (z < 2 ^ 256)%N |].

  #[global] Instance bytes32_BundledRep :
    concepts.BundledRep "monad::bytes32_t" N :=
    {| concepts.objR := bytes32R |}.

  Lemma u256_words_length n :
    length (u256_words n) = 4%nat.
  Proof.
    reflexivity.
  Qed.

  Opaque u256_words u256_word_cellsR u256_words_arrayR u256R.

  Lemma bytes32_be_values_from_length len z :
    length (bytes32_be_values_from len z) = len.
  Proof.
    induction len; simpl; congruence.
  Qed.

  Lemma bytes32_be_values_length z :
    length (bytes32_be_values z) = 32%nat.
  Proof.
    apply bytes32_be_values_from_length.
  Qed.

  Opaque bytes32_be_values_from bytes32_be_values.

  #[global] Instance bytes32R_cfractional : CFractional1 bytes32R.
  Proof.
    intros z.
    unfold bytes32R, evmc_bytes32_wordR, evmc_bytes32_bytesR.
    apply _.
  Qed.

  #[global] Instance bytes32R_as_cfractional :
    AsCFractional1 bytes32R.
  Proof.
    solve_as_cfrac.
  Qed.

  Opaque evmc_bytes32_bytesR.

  Definition evmc_bytes32R (q : cQp.t) : Rep :=
    evmc_bytes32_wordR q 0.

  Lemma evmc_bytes32R_zero_fold
      `{MODd : storage_page_cpp.source ⊧ CU} (p : ptr) :
    p ,, o_field CU "evmc_bytes32::bytes"
      |-> arrayR Tuchar (primR Tuchar 1$m) (replicateN 32 (Vint 0))
    ** p |-> structR "evmc_bytes32"%cpp_name 1$m
    |-- p |-> evmc_bytes32R 1.
  Proof using CU Sigma.
    Transparent bytes32_be_values_from bytes32_be_values
      evmc_bytes32_bytesR.
    unfold evmc_bytes32R, evmc_bytes32_wordR,
      evmc_bytes32_bytesR, bytes32_be_values.
    cbn.
    go.
  Qed.

  Opaque bytes32_be_values_from bytes32_be_values evmc_bytes32_bytesR.

  Definition evmc_bytes32R_zero_fold_B
      `{MODd : storage_page_cpp.source ⊧ CU} p :=
    [BWD] (evmc_bytes32R_zero_fold p).

  Lemma evmc_bytes32R_zero_unfold
      `{MODd : storage_page_cpp.source ⊧ CU} (p : ptr) :
    p |-> evmc_bytes32R 1
    |--
    p ,, o_field CU "evmc_bytes32::bytes"
      |-> arrayR Tuchar (primR Tuchar 1$m) (replicateN 32 (Vint 0))
    ** p |-> structR "evmc_bytes32"%cpp_name 1$m.
  Proof using CU Sigma.
    Transparent bytes32_be_values_from bytes32_be_values
      evmc_bytes32_bytesR.
    unfold evmc_bytes32R, evmc_bytes32_wordR,
      evmc_bytes32_bytesR, bytes32_be_values.
    cbn.
    go.
  Qed.

  Opaque bytes32_be_values_from bytes32_be_values evmc_bytes32_bytesR.

  Definition evmc_bytes32R_zero_unfold_F
      `{MODd : storage_page_cpp.source ⊧ CU} p :=
    [FWD] (evmc_bytes32R_zero_unfold p).

cpp.spec "monad::bytes32_t::bytes32_t(const monad::bytes32_t&)" from storage_page_cpp.source as bytes32_copy_ctor_spec with (fun (this:ptr) =>
  \arg{otherp: ptr} "other" (Vref otherp)
  \prepost{(q: Qp) (v: Corelib.Numbers.BinNums.N)}
      otherp |-> bytes32R (cQp.mut q) v
  \post this |-> bytes32R (cQp.mut 1) v
).

cpp.spec "monad::bytes32_t::~bytes32_t()" from storage_page_cpp.source as bytes32_dtor_spec with (fun (this:ptr) =>
  \pre{v} this |-> bytes32R (cQp.mut 1) v
  \post emp
).

cpp.spec "monad::bytes32_t::bytes32_t(const evmc_bytes32&)"
  from storage_page_cpp.source as bytes32_evmc_bytes32_ctor_spec with (
    fun this : ptr =>
      \arg{initp : ptr} "" (Vref initp)
      \prepost initp |-> evmc_bytes32R 1
      \post this |-> bytes32R 1 0
  ).

cpp.spec "evmc_bytes32::~evmc_bytes32()"
  from storage_page_cpp.source as evmc_bytes32_dtor_spec with (
    fun this : ptr =>
      \pre this |-> evmc_bytes32R 1
      \post emp
  ).

cpp.spec "monad::bytes32_t::operator=(const monad::bytes32_t&)"
  from storage_page_cpp.source as bytes32_assign_spec with (
    fun this : ptr =>
      \arg{otherp : ptr} "" (Vref otherp)
      \pre{old : N} this |-> bytes32R 1 old
      \prepost{qother v} otherp |-> bytes32R qother v
      \post[Vref this] this |-> bytes32R 1 v
  ).

cpp.spec
  "monad_assertion_failed"
  from storage_page_cpp.source as monad_assertion_failed_spec with (
    \arg{exprp : ptr} "" (Vptr exprp)
    \arg{funcp : ptr} "" (Vptr funcp)
    \arg{filep : ptr} "" (Vptr filep)
    \arg{line : Z} "" (Vint line)
    \arg{msgp : ptr} "" (Vptr msgp)
    \pre [| False |]
    \post emp
  ).

#[global] Instance : LearnEq2 u256R := ltac:(solve_learnable).

  Lemma observeBytes32 (bp:ptr) q v:
    Observe (type_ptr "monad::bytes32_t" bp)
            (bp |-> bytes32R q v).
  Proof using.
    unfold bytes32R.
    apply _.
  Qed.

  Definition observeBytes32F r q v := @observe_fwd _ _ _ (observeBytes32 r q v).

  Lemma observeBytes32Range (q : cQp.t) (v : N) :
    Observe (pureR [| (v < 2 ^ 256)%N |]) (bytes32R q v).
  Proof using.
    unfold bytes32R.
    apply _.
  Qed.

  Definition observeBytes32RangeF (q : cQp.t) (v : N) :=
    ltac:(mk_at_obs_fwd (observeBytes32Range q v)).

  Lemma observeU256 (bp:ptr) q v:
    Observe (type_ptr u256t bp)
            (bp |-> u256R q v).
  Proof using.
    apply _.
  Qed.

  Definition observeU256F r q v := @observe_fwd _ _ _ (observeU256 r q v).

  Lemma observeU256Range (q : cQp.t) (v : N) :
    Observe (pureR [| (v < 2 ^ 256)%N |]) (u256R q v).
  Proof using.
    apply _.
  Qed.

  Definition observeU256RangeF (q : cQp.t) (v : N) :=
    ltac:(mk_at_obs_fwd (observeU256Range q v)).

#[global] Instance : LearnEq2 bytes32R := ltac:(solve_learnable).

#[global] Instance fsksdjfk q1 q2 :
  Refine1 false false (u256R q1 = u256R q2) [q1 = q2] :=
  ltac:(constructor; auto).

End with_Sigma.

#[global] Hint Rewrite @lookup_empty @map_id : syntactic.

#[global] Hint Rewrite @map_map @nth_error_map : syntactic.

#[global] Opaque
  u256_words
  u256_word_cellsR
  u256_words_arrayR
  u256R
  bytes32_be_values_from
  bytes32_be_values
  evmc_bytes32_wordR
  bytes32R
  evmc_bytes32R.
#[global] Hint Opaque
  u256_words
  u256_word_cellsR
  u256_words_arrayR
  u256R
  bytes32_be_values_from
  bytes32_be_values
  evmc_bytes32_wordR
  bytes32R
  evmc_bytes32R : sl_opacity.

#[global] Hint Resolve observeBytes32F observeBytes32RangeF
  observeU256F observeU256RangeF : sl_opacity.

#[global] Hint Opaque specify.exact.method : sl_opacity.

#[global] Hint Opaque monad_assertion_failed_spec : sl_opacity.
#[global] Hint Opaque bytes32_evmc_bytes32_ctor_spec : sl_opacity.
#[global] Hint Opaque evmc_bytes32_dtor_spec : sl_opacity.
#[global] Hint Opaque bytes32_assign_spec : sl_opacity.

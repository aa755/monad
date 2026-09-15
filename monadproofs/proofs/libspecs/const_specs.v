Set Default Goal Selector "!".

(*
  Sound const-ownership rules for concrete Monad value representations.

  [wp_const] changes the constness carried by every subobject of a C++ object.
  Generic array traversal is independent of a translation unit. Rules for
  complete classes are proved against include-only translation units, because
  BRiCk checks their field and base-class layouts against a concrete type
  table.  [const.CONST] then transports each rule to any larger type table.
*)

Require Import monad.proofs.exec_specs.
Require Import monad.proofs.libspecs.const_tu.inc_bytes_cpp.
Require Import monad.proofs.libspecs.const_tu.inc_uint256_cpp.
Require Import skylabs.auto.cpp.hints.const.
Require Import skylabs.auto.cpp.proof.

Import cQp_compat.
Import exec_specs.
Import linearity.

(** Keep only the generated layouts used by a const rule.  An include-only
    translation unit contains many incidental standard-library declarations;
    requiring all of them to occur in every client would make the rule
    unusable even when the layouts it actually traverses agree exactly. *)
Fixpoint selected_types
    (tu : translation_unit) (names : list name) : type_table :=
  match names with
  | [] => NM.empty GlobDecl
  | nm :: names' =>
      match tu.(types) !! nm with
      | Some decl => NM.add nm decl (selected_types tu names')
      | None => selected_types tu names'
      end
  end.

Definition with_selected_types
    (tu : translation_unit) (names : list name) : translation_unit :=
  {| symbols := tu.(symbols);
     types := selected_types tu names;
     namespace_aliases := tu.(namespace_aliases);
     initializer := tu.(initializer);
     asserts := tu.(asserts);
     abi := tu.(abi);
     msymbols := tu.(msymbols);
     mtypes := tu.(mtypes);
     maliases := tu.(maliases);
     minstances := tu.(minstances) |}.

Definition uint256_const_tu : translation_unit :=
  with_selected_types inc_uint256_cpp.source
    [exec_specs.u256_words_array_name;
     "monad::uint256_t"%cpp_name].

Definition bytes32_const_tu : translation_unit :=
  with_selected_types inc_bytes_cpp.source
    ["evmc_bytes32"%cpp_name;
     "monad::bytes32_t"%cpp_name].

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Local Transparent
    u256_words
    u256_word_cellsR
    u256_words_arrayR
    u256R
    bytes32_be_values_from
    bytes32_be_values
    evmc_bytes32_bytesR
    evmc_bytes32_wordR
    bytes32R.

  Lemma arrayR_const_body
      (tu : translation_unit) {A : Type} (ety : type)
      (R : cQp.t -> A -> Rep)
      (R_const : forall value,
          const.CONST tu ety (fun q => R q value))
      (values : list A) (p : ptr) (from to : bool)
      (m : translation_unit) (Q : mpred) :
    type_table_le tu.(types) m.(types) ->
    p |-> arrayR ety (R (cQp.mk from 1)) values
    |-- (p |-> arrayR ety (R (cQp.mk to 1)) values -* Q) -*
        fold_left
          (fun Q0 (i : N) =>
             wp_const m (cQp.mk from 1) (cQp.mk to 1)
               (p .[ ety ! Z.of_N i ]) ety Q0)
          (seqN 0 (N.of_nat (length values))) (|={top}=> Q)%I.
  Proof.
    intros Hmodule.
    revert p Q.
    induction values using rev_ind.
    { intros p Q.
      change (N.of_nat 0) with 0%N.
      rewrite seqN_0 /=.
      rewrite !arrayR_nil.
      rewrite -!fupd_intro.
      go. }
    intros p Q.
    rewrite !arrayR_snoc !_at_sep !_at_offsetR.
    rewrite app_length /= Nat.add_1_r Nat2N.inj_succ.
    rewrite seqN_S_end_app fold_left_app /=.
    rewrite N.add_0_l nat_N_Z.
    normalize_ptrs.
    set (Q' :=
      fold_left
        (fun Q0 (i : N) =>
           wp_const m (cQp.mk from 1) (cQp.mk to 1)
             (p .[ ety ! Z.of_N i ]) ety Q0)
        (seqN 0 (N.of_nat (length values))) (|={top}=> Q)%I).
    apply bi.wand_intro_l.
    rewrite !_at_sep.
    rewrite (R_const x (p .[ ety ! length values ])
      from to m Q' Hmodule).
    rewrite (IHvalues p Q).
    go.
  Qed.

  Lemma arrayR_const_full
      (tu : translation_unit) {A : Type} (ety : type)
      (R : cQp.t -> A -> Rep)
      (Hety : erase_qualifiers ety = ety)
      (R_const : forall value,
          const.CONST tu ety (fun q => R q value))
      (values : list A) :
    const.CONST tu (Tarray ety (N.of_nat (length values)))
      (fun q => arrayR ety (R q) values).
  Proof.
    intros p from to m Q Hmodule.
    rewrite -wp_const_intro /= Hety.
    rewrite -fupd_intro.
    exact (arrayR_const_body tu ety R R_const values
      p from to m Q Hmodule).
  Qed.

  Lemma ulong_uintR_const word :
    const.CONST uint256_const_tu Tulong
      (fun q => primR Tulong q (Vn word)).
  Proof.
    const.prove.
    go.
  Qed.

  Lemma u256_word_cells_const n :
    const.CONST uint256_const_tu (Tarray Tulong 4)
      (fun q => arrayR Tulong
        (fun word => primR Tulong q (Vn word)) (u256_words n)).
  Proof.
    replace 4%N with (N.of_nat (length (u256_words n))).
    2: { rewrite u256_words_length. reflexivity. }
    exact (arrayR_const_full uint256_const_tu Tulong
      (fun q word => primR Tulong q (Vn word)) eq_refl
      ulong_uintR_const (u256_words n)).
  Qed.

  Definition u256_word_cells_const_C :=
    [CANCEL] u256_word_cells_const.

  #[local] Hint Resolve u256_word_cells_const_C : sl_opacity.

  Lemma u256_word_cellsR_const n :
    const.CONST uint256_const_tu (Tarray Tulong 4)
      (fun q => u256_word_cellsR q n).
  Proof.
    const.prove.
    unfold u256_word_cellsR.
    rewrite !_at_sep.
    rewrite (u256_word_cells_const n p from to uint256_const_tu
      (p |-> (type_ptrR (Tarray Tulong 4) **
       arrayR Tulong
         (fun word => primR Tulong (cQp.mk to 1) (Vn word))
         (u256_words n))) ltac:(reflexivity)).
    go.
  Qed.

  Definition u256_word_cellsR_const_C :=
    [CANCEL] u256_word_cellsR_const.

  #[local] Hint Resolve u256_word_cellsR_const_C : sl_opacity.

  Lemma u256_words_arrayR_const n :
    const.CONST uint256_const_tu
      (Tnamed exec_specs.u256_words_array_name)
      (fun q => u256_words_arrayR q n).
  Proof.
    const.prove.
    unfold u256_words_arrayR.
    go using u256_word_cellsR_const_C.
  Qed.

  Definition u256_words_arrayR_const_C :=
    [CANCEL] u256_words_arrayR_const.

  #[local] Hint Resolve u256_words_arrayR_const_C : sl_opacity.

  Lemma u256R_const :
    const.CONST1 uint256_const_tu "monad::uint256_t" u256R.
  Proof.
    const.prove.
    unfold u256R.
    go using u256_words_arrayR_const_C.
  Qed.

  Definition u256R_const_C := [CANCEL] u256R_const.

  Lemma uchar_primR_const value :
    const.CONST bytes32_const_tu Tuchar
      (fun q => primR Tuchar q value).
  Proof.
    const.prove.
    go.
  Qed.

  Lemma bytes32_byte_array_const z :
    const.CONST bytes32_const_tu (Tarray Tuchar 32)
      (fun q => arrayR Tuchar (primR Tuchar q) (bytes32_be_values z)).
  Proof.
    replace 32%N with (N.of_nat (length (bytes32_be_values z))).
    2: { rewrite bytes32_be_values_length. reflexivity. }
    apply arrayR_const_full.
    { reflexivity. }
    exact uchar_primR_const.
  Qed.

  Definition bytes32_byte_array_const_C :=
    [CANCEL] bytes32_byte_array_const.

  #[local] Hint Resolve bytes32_byte_array_const_C : sl_opacity.

  Lemma evmc_bytes32_bytesR_const z :
    const.CONST bytes32_const_tu (Tarray Tuchar 32)
      (fun q => evmc_bytes32_bytesR q z).
  Proof.
    const.prove.
    unfold evmc_bytes32_bytesR.
    rewrite !_at_sep.
    rewrite (bytes32_byte_array_const z p from to bytes32_const_tu
      (p |-> (type_ptrR (Tarray Tuchar 32) **
       arrayR Tuchar (primR Tuchar (cQp.mk to 1))
         (bytes32_be_values z))) ltac:(reflexivity)).
    go.
  Qed.

  Definition evmc_bytes32_bytesR_const_C :=
    [CANCEL] evmc_bytes32_bytesR_const.

  #[local] Hint Resolve evmc_bytes32_bytesR_const_C : sl_opacity.

  Opaque bytes32_be_values_from bytes32_be_values evmc_bytes32_bytesR.

  Lemma bytes32R_const :
    const.CONST1 bytes32_const_tu "monad::bytes32_t" bytes32R.
  Proof.
    const.prove.
    unfold bytes32R, evmc_bytes32_wordR.
    go using evmc_bytes32_bytesR_const_C.
  Qed.

  Definition bytes32R_const_C := [CANCEL] bytes32R_const.

End with_Sigma.

#[global] Hint Resolve u256R_const_C bytes32R_const_C : sl_opacity.

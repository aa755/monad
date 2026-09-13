(** Remaining inheritance case for BRiCk #156.

    [struct_byte_write.v] proves the direct-member version. This program adds
    one empty derived class, as in Monad's bytes32_t/evmc_bytes32 hierarchy.
    The layout table determines the base's offset, but the current public
    [eval_offset] interface does not connect [o_base] to that table.

    This is a diagnostic, not an assumed C++ proof. The aborted goal below
    exports no declaration and adds no axiom. *)
From Stdlib Require Import List ZArith.
Require Import skylabs.auto.cpp.proof.
Require Import skylabs.lang.cpp.logic.object_repr.
Require Import skylabs.lang.cpp.logic.layout.
Require Import skylabs.lang.cpp.parser.plugin.cpp2v.
Require Import monad.brickmisc.upstream.scalar_bytes.

Import linearity.

Set Default Goal Selector "!".

cpp.prog source prog cpp:{{
  struct Base { unsigned char bytes[2]; };
  struct Word : Base {};
  unsigned char inherited_byte_write(Word (&words)[2]) {
    auto p = reinterpret_cast<unsigned char *>(&words);
    p[2] = 7;
    return words[1].bytes[0];
  }
}}.

Section with_module.
  Context {CU : genv} {MODd : source ⊧ CU}.

  Lemma base_layout_offset : parent_offset CU "Word" "Base" = Some 0%Z.
  Proof using MODd.
    apply (parent_offset_genv_compat (tu := source)).
    vm_compute. reflexivity.
  Qed.

  (** The analogous field-offset goal is handled by [eval_o_field]. A rule
      for [o_base] would let the already-proved byte transport lemmas use
      [base_layout_offset], without equating pointers by numeric address. *)
  Goal eval_offset CU (o_base CU "Word" "Base") = Some 0%Z.
    Search (eval_offset _ (o_base _ _ _)).
    Search (ptr_cong _ (_ ,, o_base _ _ _) _).
  Abort.

  (** Alternative checked: [struct_to_raw] handles bases syntactically, but
      [raw_bytes_of_struct_wf_base] only determines the base byte-list length.
      [raw_bytes_of_struct_offset] determines contents only for fields, not
      bases. Moreover there is no introduction rule for reconstructing
      [raw_bytes_of_struct] after the writer has changed the bytes.

      Thus [struct_to_raw] alone does not currently supply the missing
      inherited-byte correspondence, in either direction. These searches are
      retained to make the exact public API used in this diagnosis inspectable. *)
  Search raw_bytes_of_struct.
End with_module.

(** Keeping every witness resolves the ownership part, but not the pointer
    correspondence. This conditional equivalence isolates those two tasks.
    [Hlocation] is an explicit premise, not an axiom or a claimed derivation
    from the layout table. No C++ correctness theorem is asserted here. *)
Section with_ownership.
  Context `{Sigma : cpp_logic} {CU : genv} {MODd : source ⊧ CU}.

  Lemma inherited_bytes_with_location (p : ptr) (q : cQp.t) (bytes : list N) :
    length bytes = 2%nat ->
    ptr_cong CU
      (p ,, o_base CU "Word" "Base" ,, o_field CU "Base::bytes") p ->
    p |-> structR "Word" q **
    p ,, o_base CU "Word" "Base" |-> structR "Base" q **
    p ,, o_base CU "Word" "Base" ,, o_field CU "Base::bytes" |->
      (type_ptrR (Tarray Tuchar 2) **
       arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes)
    -|-
    p |-> structR "Word" q **
    p ,, o_base CU "Word" "Base" |-> structR "Base" q **
    p ,, o_base CU "Word" "Base" ,, o_field CU "Base::bytes" |->
      type_ptrR (Tarray Tuchar 2) **
    p |-> arrayR Tuchar (fun b : N => primR Tuchar q (Vn b)) bytes.
  Proof using MODd.
    intros Hlength Hlocation.
    assert (Hnonempty : bytes <> []) by (intro H; subst; discriminate).
    assert (Hsize : size_of CU "Word" = Some (N.of_nat (length bytes))).
    {
      rewrite Hlength.
      apply (sizeof.prove_size_named source). vm_compute. reflexivity.
    }
    assert (Hfieldsize : size_of CU (Tarray Tuchar 2) =
      Some (N.of_nat (length bytes))) by (rewrite Hlength; reflexivity).
    split'.
    {
      go.
      wapply (byte_array_at_congruent_pointer
        (p ,, o_base CU "Word" "Base" ,, o_field CU "Base::bytes")
        p q bytes Hlocation).
      go using ([BWD] object_byte_array_witness "Word" p bytes Hnonempty Hsize).
    }
    {
      go.
      wapply (byte_array_at_congruent_pointer p
        (p ,, o_base CU "Word" "Base" ,, o_field CU "Base::bytes")
        q bytes (symmetry Hlocation)).
      go using ([BWD] object_byte_array_witness (Tarray Tuchar 2)
        (p ,, o_base CU "Word" "Base" ,, o_field CU "Base::bytes")
        bytes Hnonempty Hfieldsize).
    }
  Qed.
End with_ownership.

Set Printing Fully Qualified.
Print Assumptions inherited_bytes_with_location.
Unset Printing Fully Qualified.

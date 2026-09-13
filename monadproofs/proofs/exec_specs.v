Set Default Goal Selector "!".

Require Import skylabs.auto.cpp.proof.
Require Import skylabs.brick.libstdcpp.allocator.spec.
Require Import skylabs.brick.libstdcpp.cassert.spec.
Require Import skylabs.brick.libstdcpp.vector.spec.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.
Require Import skylabs.brick.libstdcpp.algorithms.spec.
Require Import skylabs.brick.libstdcpp.new.spec_exc.

Require Import skylabs.auto.cpp.prelude.test.

Require Import QArith.
Require Import Lens.Elpi.Elpi.
Require Import skylabs.lang.cpp.cpp.
Require Import stdpp.gmap.
Require Import monad.proofs.misc.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import monad.asts.exb.
Require Import monad.asts.reserve_balance_cpp.
Require Import monad.asts.state_cpp.
Require Export skylabs.auto.cpp.spec.
From AAC_tactics Require Import AAC.

Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.fiber_specs.
Require Import monad.proofs.libspecs.vector_delete.
Require Import monad.proofs.libspecs.span_specs.
Require Export monad.proofs.libspecs.pair_specs.
Require Export monad.proofs.libspecs.ankerl_specs.
Require Import monad.proofs.libspecs.immer_specs.
Require Import monad.proofs.libspecs.deque_specs.
Require Import monad.proofs.libspecs.ranges_specs.
Require Import monad.proofs.libspecs.outcome_specs.
Require Import monad.proofs.libspecs.outcome_status_code_specs.
Import optional_specs.
Import immer_specs.
Import fiber_specs.
Import vector_delete.
Import cQp_compat.
#[local] Open Scope lens_scope.
Set Warnings "+sl-impossible-patterns".

(*
#[only(lens)] derive block.block_account.
#[only(lens)] derive AccountM.
*)
Notation u256t := ("monad::uint256_t"%cpp_type).

Notation resultn ty :=
  (outcome_result_name
     ty outcome_error_ty
     (outcome_status_code_throw_policy_ty ty outcome_error_ty)).

  (* ------------------------------------------------------------------------- *)
  (* 1) Bundle fields of AccountSubstate into a record                         *)
  (* ------------------------------------------------------------------------- *)
  Record AccountSubstateModel : Type := {
    asm_destructed     : bool;
    asm_touched        : bool;
    asm_accessed       : bool;
    asm_accessed_keys  : list Corelib.Numbers.BinNums.N
  }.

#[local] Open Scope Z_scope.
(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.



Record AssumptionExactness :=
  {
    min_balance: option N; (* None means exact validation *)
    nonce_exact: bool;
  }.


Record AssumedPreTxAccountState :=
  {
    preTxState : option AccountM; (* None means the account did not exist when read from BlockState. but the account was referenced, e.g. its balance was read to be 0 *)
    preTxStorage : list (N * N); (* lazy cache of original storage slots read by OriginalAccountState *)
    assumExactness: AssumptionExactness;
  }.
    
Record UpdatedAccountState :=
  {
    postTxState: option AccountM; (* None iff the account committed suicide and we are after destruct_suicides in execute_final.  rename postTxState to currentState: as this may be used even before tx has finished *)
    substateModel : AccountSubstateModel;
  }.
    
Record TxAssumptionsAndUpdates :=
  {
    preAssumption: AssumedPreTxAccountState;
    originalLoc: ptr;
    txUpdates : option (ptr*(ptr *UpdatedAccountState)); (* None means, the tx did not make any updates to this account. outer ptr is the location in the map, inner ptr is the location of the PartialAccountState in the VersionStack *)
  }.


Definition check_min_balance_ok (cur debit: N) : bool :=
  bool_decide (debit <= cur)%N.

Definition min_balance_update
           (old: AssumptionExactness)
           (orig cur debit: N) : AssumptionExactness :=
  if check_min_balance_ok cur debit then
    match min_balance old with
    | None => old
    | Some old_min =>
        (* Mirrors State::check_account_min_balance:
           if cur >= debit, tighten min_balance using (orig - (cur - debit)). *)
        let diff := N.sub cur debit in
        let new_min :=
          if N.ltb diff orig
          then N.max old_min (N.sub orig diff)
          else old_min in
        {| min_balance := Some new_min;
           nonce_exact := nonce_exact old |}
    end
  else
    (* Mirrors State::check_account_min_balance:
       if cur < debit, switch to exact-balance validation. *)
    {| min_balance := None;
       nonce_exact := nonce_exact old |}.

Definition update_assum_exactness_at
           (addr: evm.address)
           (f: AssumptionExactness -> AssumptionExactness)
           (m: MapModel evm.address AssumedPreTxAccountState)
  : MapModel evm.address AssumedPreTxAccountState :=
  map (fun p =>
         let '(addr', (loc, aps)) := p in
         if bool_decide (addr' = addr) then
           (addr', (loc,
                    {| preTxState := preTxState aps;
                       preTxStorage := preTxStorage aps;
                       assumExactness := f (assumExactness aps) |}))
         else p) m.

Definition exact_balance_update
           (old: AssumptionExactness) : AssumptionExactness :=
  {| min_balance := None;
     nonce_exact := nonce_exact old |}.

Module OneTbbMap. Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

  (* TODO: generalize over MapOriginalR and MapCurrentR and specialize with AccountStatR, move that up *)
  Definition Rauth {K V:Type} (tykey tyval: type) (khash: K -> N) {eqd: EqDecision K}
           (krep : Qp -> K -> Rep) (* not sure whether this needs to be fractional *)
           (vrep : Qp -> V -> Rep) (* fraction needed as there can be multiple concrrent readers of the value *)
           (* CFrational vrep *)
           (q: stdpp.numbers.Qp) (* one::tbb::concurrent_map itself is used as a value time (storage delta in StateDelta) so Rauth itself must be fractional. q<1 means can only read. unlike Rfrag, we can depend on the value being m *)
           (m: list (K*V))
    : Rep. Proof. Admitted.
(*  structR (Ninst "oneapi::tbb::concurrent_hash_map" [Atype tykey; Atype tyval]) (1/2). *)

  (* TODO: generalize over MapOriginalR and MapCurrentR and specialize with AccountStatR, move that up *)
  Definition Rfrag {K V:Type} (tykey tyval: type) (khash: K -> N) `{EqDecidable K}
           (krep : K -> Rep)
           (vrep : V -> Rep)
           (q: stdpp.numbers.Qp): Rep. Proof. Admitted.
 (*  structR (Ninst "oneapi::tbb::concurrent_hash_map" [Atype tykey; Atype tyval]) (q/2). *)
  
End with_Sigma. End OneTbbMap.


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
      `{MODd : state_cpp.source ⊧ CU} (p : ptr) :
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
      `{MODd : state_cpp.source ⊧ CU} p :=
    [BWD] (evmc_bytes32R_zero_fold p).

  Lemma evmc_bytes32R_zero_unfold
      `{MODd : state_cpp.source ⊧ CU} (p : ptr) :
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
      `{MODd : state_cpp.source ⊧ CU} p :=
    [FWD] (evmc_bytes32R_zero_unfold p).

  Definition DeltaR {T:Type} (ty: type) (Trep : Qp-> T ->  Rep) (q:Qp) (beforeafter: T * T) : Rep. Proof. Admitted.

(* A simplistic layout of the "accessed_storage_" table: *)
  Definition AccessedKeysR (q: stdpp.numbers.Qp)
           (keys: list Corelib.Numbers.BinNums.N)
    : skylabs.lang.cpp.logic.rep_defs.Rep :=
    anyR
      "ankerl::unordered_dense::v4_1_0::detail::table<monad::bytes32_t, void, ankerl::unordered_dense::v4_1_0::hash<monad::bytes32_t, void>, std::equal_to<monad::bytes32_t>, std::allocator<monad::bytes32_t>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 0b>"%cpp_type
      (cQp.mut q).
  
  Definition StorageMapKeyTy : type :=
    "monad::bytes32_t"%cpp_type.

  Definition StorageMapHashName : name :=
    Ninst
      (Nscoped
        (Nscoped
          (Nscoped (Nglobal (Nid "ankerl")) (Nid "unordered_dense"))
          (Nid "v4_1_0"))
        (Nid "hash"))
      [Atype StorageMapKeyTy; Atype Tvoid].

  Definition StorageMapEqName : name :=
    Ninst (Nscoped (Nglobal (Nid "std")) (Nid "equal_to"))
      [Atype StorageMapKeyTy].

  Definition StorageMapHeapPolicyName : name :=
    Ninst (Nscoped (Nglobal (Nid "immer")) (Nid "free_list_heap_policy"))
      [Atype (Tnamed (Nscoped (Nglobal (Nid "immer")) (Nid "cpp_heap")));
       Avalue (Eint 1024 Tulong)].

  Definition StorageMapMemoryPolicyName : name :=
    Ninst (Nscoped (Nglobal (Nid "immer")) (Nid "memory_policy"))
      [Atype (Tnamed StorageMapHeapPolicyName);
       Atype (Tnamed (Nscoped (Nglobal (Nid "immer")) (Nid "refcount_policy")));
       Atype (Tnamed (Nscoped (Nglobal (Nid "immer")) (Nid "spinlock_policy")));
       Atype (Tnamed (Nscoped (Nglobal (Nid "immer")) (Nid "no_transience_policy")));
       Avalue (Eint 0 Tbool);
       Avalue (Eint 1 Tbool)].

  Definition StorageMapName : name :=
    Ninst (Nscoped (Nglobal (Nid "immer")) (Nid "map"))
      [Atype StorageMapKeyTy;
       Atype StorageMapKeyTy;
       Atype (Tnamed StorageMapHashName);
       Atype (Tnamed StorageMapEqName);
       Atype (Tnamed StorageMapMemoryPolicyName);
       Avalue (Eint 5 Tuint)].

  Definition StorageMapTy : type := Tnamed StorageMapName.

  Definition StorageMapR (q: Qp)
             (m: list (N*N)) : Rep :=
    immer_specs.ImmerMapR StorageMapTy
      bytes32R
      (fun q => bytes32R (cQp.mut q)) q m.


  Definition account_code (am: AccountM) : evm.program :=
    block.block_account_code (coreAc am).

  Definition code_entry_of_updates
      (updates: list (ptr * UpdatedAccountState))
    : option (N * evm.program) :=
    match updates with
    | (_, up) :: _ =>
        match postTxState up with
        | Some am =>
            let code := account_code am in
            Some (code_hash_of_program code, code)
        | None => None
        end
    | [] => None
    end.

Definition code_entries_of_state
      (m: MapModel evm.address (list (ptr * UpdatedAccountState)))
    : list (N * evm.program) :=
    fold_right (fun kv acc =>
      let '(_, (_, updates)) := kv in
      match code_entry_of_updates updates with
      | Some kv' => kv' :: acc
      | None => acc
      end) [] m.

  Definition code_entry_of_assumed
      (aps: AssumedPreTxAccountState) : option (N * evm.program) :=
    match preTxState aps with
    | Some am =>
        let code := account_code am in
        Some (code_hash_of_program code, code)
    | None => None
    end.

  Definition code_entries_of_preTxAssumed
      (m: MapModel evm.address AssumedPreTxAccountState)
    : list (N * evm.program) :=
    fold_right (fun kv acc =>
      let '(_, (_, aps)) := kv in
      match code_entry_of_assumed aps with
      | Some kv' => kv' :: acc
      | None => acc
      end) [] m.

  Definition IncarnationR (q : cQp.t) (i: Indices): Rep. Proof. Admitted.

  #[global] Instance observe_IncarnationR_type_ptr q idx :
    Observe (type_ptrR (Tnamed "monad::Incarnation"%cpp_name))
      (IncarnationR q idx).
  Proof using.
    Admitted.

  Definition observe_IncarnationR_type_ptr_F :=
    ltac:(mk_at_obs_fwd observe_IncarnationR_type_ptr).

  (* ------------------------------------------------------------------------- *)
  (* 2) AccountSubstateR with structR                                          *)
  (* ------------------------------------------------------------------------- *)
  Definition AccountSubstateR
             (q: stdpp.numbers.Qp)
             (m: AccountSubstateModel)
    : skylabs.lang.cpp.logic.rep_defs.Rep :=
    _field "AccountSubstate::destructed_"         |-> boolR (cQp.mut q) m.(asm_destructed)
    ** _field "AccountSubstate::touched_"          |-> boolR (cQp.mut q) m.(asm_touched)
    ** _field "AccountSubstate::accessed_"         |-> boolR (cQp.mut q) m.(asm_accessed)
    ** _field "AccountSubstate::accessed_storage_" |-> AccessedKeysR q m.(asm_accessed_keys)
    ** structR "monad::AccountSubstate"%cpp_name  (cQp.mut q).

  (* ------------------------------------------------------------------------- *)
  (* 3) AccountR with structR                                                   *)
  (* ------------------------------------------------------------------------- *)
  Definition AccountR
             (q : cQp.t)
             (ac: AccountM) : Rep :=
    let ba := coreAc ac in
    [| ac.(balance) = w256_to_N ba.(EVMOpSem.block.block_account_balance) |]
    ** _field "monad::Account::balance"       |-> u256R q (w256_to_N ba.(EVMOpSem.block.block_account_balance))
    ** _field "monad::Account::code_hash"  |-> bytes32R q (code_hash_of_program ba.(EVMOpSem.block.block_account_code))
    ** _field "monad::Account::nonce"      |-> primR "unsigned long" q (w256_to_Z ba.(EVMOpSem.block.block_account_nonce))
    ** _field "monad::Account::incarnation"|-> IncarnationR q (incarnation ac)
    ** structR "monad::Account"%cpp_name q.

  #[global] Instance account_bundled_rep :
    concepts.BundledRep "monad::Account" AccountM :=
    {| concepts.objR := AccountR |}.

  (* Account's implicit move copies its scalar/value members; it does not
     clear the source account. *)
  #[global] Instance account_moved_value :
    concepts.MovedValue "monad::Account" AccountM :=
    {| concepts.moved := eq |}.

  Definition addressR (q: Qp) (a: evm.address): Rep. Proof. Admitted.
  Definition optionAddressR (q:Qp) (oaddr: option evm.address): Rep :=
    optional_specs.optionR "monad::Address"
      (fun q' => addressR (cQp.frac q')) (cQp.mut q) oaddr.

  Definition bytes32_to_w256 (n : N) : keccak.w256 :=
    Z_to_w256 (Z.of_N n).

  Definition account_storage_value (ac : AccountM) (key : N) : N :=
    w256_to_N
      (block.block_account_storage (coreAc ac) (bytes32_to_w256 key)).

  Definition storageMapOf (p : option AccountM) : list (N * N) :=
    match p with
    | Some ac => map (fun key => (key, account_storage_value ac key))
                   (relevantKeys ac)
    | None => []
    end.
  
  Definition AccountStateRcore (q: Qp) (origp: option AccountM) : Rep :=
    (_field "monad::AccountState::account_"
         |-> optional_specs.optionR
              "monad::Account"%cpp_type
              AccountR
              q
              origp
    ** _field "monad::AccountState::storage_"
              |-> StorageMapR q (storageMapOf origp)
   ** (Exists transient_map, _field "monad::AccountState::transient_storage_"
                                          |-> StorageMapR q transient_map)
    ** structR "monad::AccountState"%cpp_name (cQp.mut q)).

  Definition unusedAccountSubstate : AccountSubstateModel :=
    {| asm_destructed := false;  asm_touched := false;  asm_accessed := false;  asm_accessed_keys := [] |}.
    
  Definition OriginalAccountStateR
    (q: Qp)
    (os: AssumedPreTxAccountState) : Rep :=
    let asm := assumExactness os in 
    structR "monad::OriginalAccountState"%cpp_name (cQp.mut q)
    ** (o_base CU "monad::OriginalAccountState" "monad::AccountState" |->
          (_field "monad::AccountState::account_"
             |-> optional_specs.optionR
                  "monad::Account"%cpp_type
                  AccountR
                  q
                  (preTxState os)
           ** _field "monad::AccountState::storage_"
             |-> StorageMapR q (preTxStorage os)
           ** (Exists transient_map,
                _field "monad::AccountState::transient_storage_"
                  |-> StorageMapR q transient_map)
           ** structR "monad::AccountState"%cpp_name (cQp.mut q)))
(*    ** _field "monad::OriginalAccountState::validate_exact_nonce_"   |-> boolR (cQp.mut q) (nonce_exact asm) *)
    (* exact‐balance flag *)
    ** _field "monad::OriginalAccountState::validate_exact_balance_" |-> boolR (cQp.mut q)
                                                                    (~~
                                                                       (bool_decide (is_Some (min_balance asm))))
    (* min_balance_ bound *)
    ** _field "monad::OriginalAccountState::min_balance_" |->
        match min_balance asm with             
        | Some n => u256R q n
        | None =>
           Exists (nb: N),  u256R q nb
        end
        ** (o_base CU "monad::OriginalAccountState" "monad::AccountState" |->
              _base "monad::AccountState"%cpp_name "monad::AccountSubstate"%cpp_name
                           |-> AccountSubstateR q unusedAccountSubstate) (* ideally, this should be removed from the c++ class. substate fields are not relevant for original acount state: relevant only for updated state *)
    (* the struct itself 
     ** structR "monad::AccountState"%cpp_name (cQp.mut q) *).
  
  Definition UpdatedAccountStateR
    (q: Qp)
    (os: UpdatedAccountState) : Rep :=
    AccountStateRcore q (postTxState os) **
      _base "monad::AccountState"%cpp_name "monad::AccountSubstate"%cpp_name
      |-> AccountSubstateR q (substateModel os).

  Definition accountStorageDelta (beforeafter: evm.storage * evm.storage) : list (N * (N * N)). Proof. Admitted.

  Definition pairMap {A B:Type} (f: A -> B) (p : A*A) : B*B := (f (fst p), f (snd p)).

  
  Definition StateDeltaR (q:Qp) (beforeaft:  AccountM * AccountM) : Rep :=
    _field "monad::StateDelta::account" |-> DeltaR "monad::Account"
      (fun q => AccountR (cQp.mut q)) q beforeaft
    ** _field "monad::StateDelta::storage"
      |-> OneTbbMap.Rauth
           "::monad::bytes32_t"
           (Tnamed (Ninst "monad::Delta" [Atype "::monad::bytes32_t"]))
           (fun x:N => x)
           bytes32R
           (DeltaR "::monad::bytes32_t" bytes32R)
           q
           (accountStorageDelta
              (pairMap (fun x => (block.block_account_storage (coreAc x)))  beforeaft))
    ** structR "monad::StateDelta" q.

  

  Definition globalDelta (beforeAfter: evm.GlobalState * evm.GlobalState) : list (evm.address * (AccountM * AccountM)). Proof. Admitted.
  
  Definition StateDeltasR (q:Qp) (beforeAfter: evm.GlobalState * evm.GlobalState) : Rep :=
    OneTbbMap.Rauth
      "monad::Address"
      "monad::StateDelta"
      (fun a => a)
      addressR
      StateDeltaR
      q
      (globalDelta beforeAfter).

  Definition CodeDeltaR (q:Qp) (beforeAfter: evm.GlobalState * evm.GlobalState) : Rep. Proof. Admitted.
    (*
    OneTbbMap.Rauth
      "monad::Address"
      "std::shared_ptr<CodeAnalysis>"
      (fun a => Z.to_N (word160.word160ToInteger a))
      addressR
      StateDeltaR
      q
      (globalDelta beforeAfter).
  *)
End with_Sigma.
#[global] Hint Resolve
  observe_IncarnationR_type_ptr_F : sl_opacity.
 Definition CodeHash := N.
 Module BlockState. Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)


  Context (blockPreState: AugmentedState). (* BlockState is a type that makes sense in the context of a block and the state before the block  *)
  (** defines how the Coq (mathematical) state of Coq type [StateOfAccounts] is represented as a C++ datastructure in the fields of the BlockState class.
      [blockPreState] is the state at the beginning of the block.  newState
   *)
    

  Record glocs :=
    {
      cmap: gname;
    }.

  Notation Code := evm.program.

  Definition fullCodeMap (newState: AugmentedState): gmap CodeHash Code. Proof. Admitted.

  (** the code map can have more entries than what is contained in the accounts of [newStates], as computed by [fullCodeMap newStates]: e.g. in the middle of BlockState.merge. That also happens when we are running EVM historical blocks and some account was destructed at the time that used to delete the account. *)
  (** [Rauth] is the exclusive BlockState capability used by validation/merge
      operations. [Rfrag] is shareable and supports concurrent reads, which may
      observe DB/pre-block state or already-merged earlier transactions. *)
  Definition Rauth (g: glocs) (newState: AugmentedState): Rep.
  Proof using blockPreState. Admitted. (* To be defined later. something like: [_field db_ |-> DbR blockPreState ** _field deltas |-> StateDeltasR blockPreState newState] *)

  (** codeMapLb  represents all the codehash to code entries either in the Db or in BlockState. Can we move [blockPreState] to glocs? *)
  Definition Rfrag (q:Qp) (g: glocs): Rep.
  Proof using blockPreState. Admitted.

  (** this predicate has no ownership attachd. you need Rfrag or Rauth to call blockstate methods. *)
  Definition CodeMapContainsEntries (g: glocs) (entries: gmap CodeHash Code) : Rep.
  Proof using. Admitted.

  (** this predicate has no ownership attachd. you need Rfrag or Rauth to call blockstate methods. *)
  Definition CodeMapContainsKeys (g: glocs) (keys: list CodeHash) : Rep.
  Proof using. Admitted.
  
  (* TODO: move to a proofmisc file and replace by a lemma about just binary splitting *)
  Lemma split_frag {T} q g (l : list T):
    Rfrag q g -|- Rfrag (q/(N_to_Qp (1+ lengthN l))) g ** 
    ([∗ list] _ ∈ l,  (Rfrag (q*/(N_to_Qp (1+ lengthN l))) g)).
  Proof using. Admitted.

  (* TODO: move to a proofmisc file *)
  Lemma split_frag_loopinv {T} q g (l : list T) (i:nat) (prf: i=0):
    Rfrag q g -|- Rfrag (q/(N_to_Qp (1+ lengthN l))) g** 
    ([∗ list] _ ∈ (drop i l),  (Rfrag (q*/(N_to_Qp (1+ lengthN l))) g)).
  Proof using.
    subst.  autorewrite with syntactic. apply split_frag.
  Qed.

  (** if State::read_code has observed a code mapping that did not exist in State, it is guaranteed to be there when the previous tx finishes and thus we have Rauth *)
  Lemma code_map_lb (q:Qp) (g: glocs) (codeMapLb: gmap CodeHash Code) currentState:
    Observe [| codeMapLb ⊆ fullCodeMap currentState |]
      (CodeMapContainsEntries g codeMapLb ** Rauth g currentState).
  Proof. Admitted.

  Lemma code_map_lb2 (q:Qp) (g: glocs) (keys: list CodeHash) currentState:
    Observe [| keys ⊆ map fst (map_to_list (fullCodeMap currentState)) |]
      (CodeMapContainsKeys g keys ** Rauth g currentState).
  Proof. Admitted.

  Lemma duplicableCodeMapEntries (q:Qp) (g: glocs) (codeMapLb: gmap CodeHash Code):
    CodeMapContainsEntries g codeMapLb |-- CodeMapContainsEntries g codeMapLb **  CodeMapContainsEntries g codeMapLb.
  Proof. Admitted.
  
  Lemma codeMapWeaken (q:Qp) (g: glocs) (codeMapLb1 codeMapLb2: gmap CodeHash Code):
    codeMapLb2 ⊆ codeMapLb1
    -> CodeMapContainsEntries g codeMapLb1 |-- CodeMapContainsEntries g codeMapLb2.
  Proof. Admitted.
  (* FIXME: add the above analogues of 2 lemmas for CodeMapContainsKeys *)

  
End with_Sigma. End BlockState.


Record StateM :=
  {
    relaxedValidation: bool;
    preTxAssumedState: MapModel evm.address AssumedPreTxAccountState;
    newStates: MapModel evm.address (list (ptr*UpdatedAccountState)); (* head is the latest *)
    blockStatePtr: ptr;
    indices: Indices;
    blockStateGloc: BlockState.glocs;
    dbBlockStateCodeMapLb : gmap CodeHash evm.program;
    codeMap : gmap CodeHash evm.program;
  }.

Definition update_assum_exactness_state_at
           (st: StateM)
           (addr: evm.address)
           (f: AssumptionExactness -> AssumptionExactness) : StateM :=
  {| relaxedValidation := relaxedValidation st;
     preTxAssumedState := update_assum_exactness_at addr f (preTxAssumedState st);
     newStates := newStates st;
     blockStatePtr := blockStatePtr st;
    indices := indices st;
    blockStateGloc := blockStateGloc st;
    dbBlockStateCodeMapLb := dbBlockStateCodeMapLb st;
    codeMap := codeMap st;
  |}.


(* Import skylabs.lang.cpp.semantics.values.VALUES_INTF_AXIOM. *)


Open Scope cpp_name.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

   
  (* defines how [c] is represented in memory as an object of class Chain. this predicate asserts [q] ownership of the object, assuming it can be shared across multiple threads  *)
  Definition ChainR (q: Qp) (c: Chain): Rep. Proof. Admitted.

  Lemma ChainR_split_loopinv {T} q (b: Chain) (l : list T) (i:nat) (p:i=0):
    ChainR q b -|- ChainR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ (drop i l),  (ChainR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using. Admitted.

  Definition tx_nonce tx :=
    (w256_to_N (block.tr_nonce tx)).
  Definition tx_gas_limit tx :=
    (w256_to_N (block.tr_gas_limit tx)).
  Definition TransactionR (q:Qp) (tx: Transaction) : Rep :=
    structR "monad::Transaction" q **
      _field "monad::Transaction::nonce" |-> ulongR q (tx_nonce tx.1) **
      o_field CU "monad::Transaction::gas_limit" |-> ulongR q (tx_gas_limit tx.1).

  #[global] Instance learnTrRbase: LearnEq2 TransactionR:= ltac:(solve_learnable).

  Definition BheaderR (q:Qp) (hdr: BlockHeader) : Rep :=
    structR "monad::BlockHeader" q
    ** _field "monad::BlockHeader::base_fee_per_gas"
         |-> optional_specs.optionR u256t u256R (cQp.mut q)
               (base_fee_per_gas hdr)
    ** _field "monad::BlockHeader::number" |-> ulongR q  (number hdr)
    ** _field "monad::BlockHeader::beneficiary" 
         |-> addressR 1 (beneficiary hdr)
    ** _field "monad::BlockHeader::timestamp" |-> primR "unsigned long" q (timestamp hdr).
         
  Definition BlockR (q: Qp) (c: Block): Rep :=
    _field "::monad::Block::transactions" |-> VectorR (Tnamed "::monad::Transaction") (fun t => TransactionR q t) q (transactions c)
    ** _field "::monad::Block::header" |-> BheaderR q (header c)
      ** structR "::monad::Block" q.

  (* Copied from execproofs/reservebal/reserve_balance.v; TODO: delete there once proofs move. *)
  Record History {T:Type} : Type :=
    { currentBlock: T;
      parentBlock: option T;
      grandParentBlock: option T }.
  Arguments History : clear implicits.

  Record MonadChainContext : Type :=
    { senders_and_authoritiesp: History ptr;
      blocks: History Block;
      sendersp: ptr;
      authsp: ptr }.

  Definition monad_revision_ty : type :=
    "enum monad_revision"%cpp_type.

  Definition monad_address_ty : type :=
    "monad::Address"%cpp_type.

  Definition monad_uint256_ty : type :=
    "monad::uint256_t"%cpp_type.

  Definition monad_traits_ty (rev : Z) : type :=
    Tnamed ("monad::MonadTraits" .<< Avalue (Eint rev monad_revision_ty) >>)%cpp_name.

  Definition monad_chain_context_name (rev : Z) : name :=
    ("monad::ChainContext" .<< Atype (monad_traits_ty rev) >>)%cpp_name.

  Definition monad_chain_context_ty (rev : Z) : type :=
    Tnamed (monad_chain_context_name rev).

  Definition monad_chain_context_field (rev : Z) (field : string) : name :=
    (monad_chain_context_name rev .:: Nid field)%cpp_field.

  Definition sendersAndAuthorities (b: Block): list EvmAddr :=
    map sender (txsWithHdr b) ++
    flat_map
      (fun tx =>
         flat_map
           (fun oa =>
              match oa with
              | Some addr => [addr]
              | None => []
              end)
           (map del_from (authorities (tx.2))))
      (transactions b).
  Definition addressToN (a: evm.address) : N. Proof. Admitted.
  Definition address_set_table_ty : type :=
    ankerl_specs.anker_set_table_ty "monad::Address".

  Definition address_set_table_allocator_ty : type :=
    Tnamed (ankerl_specs.anker_set_allocator_name address_set_table_ty).

  #[global] Instance evmaddr : concepts.BundledRep "evmc::address" EvmAddr.
  Proof.
    constructor. intros. apply addressR; [|assumption]. exact (cQp.frac q).
  Defined.

  #[global] Instance monadaddr : concepts.BundledRep "monad::Address" EvmAddr.
  Proof.
    constructor. intros. apply addressR; [|assumption]. exact (cQp.frac q).
  Defined.

  #[global] Instance optionalrep (bty: type) (bT: Type)
    {cb: concepts.BundledRep bty bT} :
    concepts.BundledRep (Tnamed ("std::optional".<<Atype bty>>)) (option bT).
  Proof.
    constructor. intros q o.
    exact (optional_specs.optionR bty (concepts.objR bty) q o).
  Defined.

  Notation stdvector ty := (std.vector.T ty (std.allocator.T ty)).

  Definition stdallocator_source (ty : type) : type :=
    Tnamed ("std::allocator".<< Atype ty >>)%cpp_name.

  Definition stdvector_source (ty : type) : type :=
    Tnamed ("std::vector".<< Atype ty, Atype (stdallocator_source ty) >>)%cpp_name.

  #[global] Instance vectorrep (bty: type) (bT: Type)
    {cb: concepts.BundledRep bty bT} :
    concepts.BundledRep (stdvector bty) (list bT).
  Proof.
    constructor. intros q l. apply (std.vector.R bty q l).
  Defined.

  Definition txAuthoritiesDelFrom (t: Transaction) : list (option EvmAddr) :=
    map del_from (authorities (t.2)).

  Definition SenderAuthoritiesSetR (q: Qp) (addrs: list EvmAddr) : Rep :=
    ankerl_specs.AnkerSetR "monad::Address" addressToN addressR q addrs.

  Definition ptr_of_option (op : option ptr) : ptr :=
    match op with
    | Some p => p
    | None => nullptr
    end.

  Definition MonadChainContextR (q: Qp) (m: MonadChainContext) : Rep :=
    let curblock := currentBlock (blocks m) in
    let cursetp := currentBlock (senders_and_authoritiesp m) in
    let parentsetpo := parentBlock (senders_and_authoritiesp m) in
    let grandparentsetpo := grandParentBlock (senders_and_authoritiesp m) in
    structR (monad_chain_context_name 10) (cQp.mut q)
      ** _field (monad_chain_context_field 10 "grandparent_senders_and_authorities") |->
           primR
             (Tref address_set_table_ty)
             (cQp.m q) (Vptr (ptr_of_option grandparentsetpo))
      ** (match grandparentsetpo, grandParentBlock (blocks m) with
          | None, None =>
              [| (number (header curblock) <= 2)%N |]
              ** pureR (nullptr |-> SenderAuthoritiesSetR (cQp.m q) [])
          | Some grandparentsetp, Some grandparentblock =>
              ([| (2 < number (header curblock))%N |]
               ** [| grandparentsetp <> nullptr |]
               ** pureR (grandparentsetp |-> SenderAuthoritiesSetR (cQp.m q)
                                (sendersAndAuthorities grandparentblock)))
          | _, _ => pureR False
          end)
      ** _field (monad_chain_context_field 10 "parent_senders_and_authorities") |->
           primR
             (Tref address_set_table_ty)
             (cQp.m q) (Vptr (ptr_of_option parentsetpo))
      ** (match parentsetpo, parentBlock (blocks m) with
          | None, None =>
              [| (number (header curblock) <= 1)%N |]
              ** pureR (nullptr |-> SenderAuthoritiesSetR (cQp.m q) [])
          | Some parentsetp, Some parentblock =>
              ([| (1 < number (header curblock))%N |]
               ** [| parentsetp <> nullptr |]
               ** pureR (parentsetp |-> SenderAuthoritiesSetR (cQp.m q)
                                (sendersAndAuthorities parentblock)))
          | _, _ => pureR False
          end)
      ** _field (monad_chain_context_field 10 "senders_and_authorities") |->
           primR
             (Tref address_set_table_ty)
             (cQp.m q) (Vptr cursetp)
      ** pureR (cursetp |-> SenderAuthoritiesSetR (cQp.m q)
                    (sendersAndAuthorities curblock))
      ** _field (monad_chain_context_field 10 "senders") |->
          primR (Tref (stdvector_source "monad::Address")) (cQp.m q) (Vptr (sendersp m))
      ** pureR ((sendersp m) |-> std.vector.R "monad::Address" (cQp.m q) (map sender (txsWithHdr curblock)))
      ** _field (monad_chain_context_field 10 "authorities") |->
          primR (Tref (stdvector_source (stdvector_source "std::optional<monad::Address>"))) (cQp.m q) (Vptr (authsp m))
      ** pureR ((authsp m) |-> std.vector.R (stdvector "std::optional<monad::Address>") (cQp.m q)
                 (map txAuthoritiesDelFrom (transactions curblock))).

  Definition wei_per_mon : N := 1000000000000000000%N.
  Definition DefReserve : N := (10 * wei_per_mon)%N.

  Definition sender_in_block (b: Block) (addr : EvmAddr) : Prop :=
    addr ∈ map sender (txsWithHdr b).

  Definition authority_in_block (b: Block) (addr : EvmAddr) : Prop :=
    Some addr ∈ flat_map txAuthoritiesDelFrom (transactions b).

  Definition sender_in_recent_history
      (ctx : MonadChainContext) (tx : TxWithHdr) : Prop :=
    (match parentBlock (blocks ctx) with
     | Some parent => sender_in_block parent (sender tx)
     | None => False
     end) \/
    (match grandParentBlock (blocks ctx) with
     | Some grandparent => sender_in_block grandparent (sender tx)
     | None => False
     end).

  Definition delundel_in_recent_history
      (ctx : MonadChainContext) (tx : TxWithHdr) : Prop :=
    (match parentBlock (blocks ctx) with
     | Some parent => authority_in_block parent (sender tx)
     | None => False
     end) \/
    (match grandParentBlock (blocks ctx) with
     | Some grandparent => authority_in_block grandparent (sender tx)
     | None => False
     end).

  Definition sender_in_recent_historyb
      (ctx : MonadChainContext) (tx : TxWithHdr) : bool :=
    match parentBlock (blocks ctx), grandParentBlock (blocks ctx) with
    | Some parent, Some grandparent =>
        asbool (sender tx ∈ map sender (txsWithHdr parent)) ||
        asbool (sender tx ∈ map sender (txsWithHdr grandparent))
    | Some parent, None =>
        asbool (sender tx ∈ map sender (txsWithHdr parent))
    | None, Some grandparent =>
        asbool (sender tx ∈ map sender (txsWithHdr grandparent))
    | None, None => false
    end.

  Definition delundel_in_recent_historyb
      (ctx : MonadChainContext) (tx : TxWithHdr) : bool :=
    match parentBlock (blocks ctx), grandParentBlock (blocks ctx) with
    | Some parent, Some grandparent =>
        asbool (Some (sender tx) ∈ flat_map txAuthoritiesDelFrom (transactions parent)) ||
        asbool (Some (sender tx) ∈ flat_map txAuthoritiesDelFrom (transactions grandparent))
    | Some parent, None =>
        asbool (Some (sender tx) ∈ flat_map txAuthoritiesDelFrom (transactions parent))
    | None, Some grandparent =>
        asbool (Some (sender tx) ∈ flat_map txAuthoritiesDelFrom (transactions grandparent))
    | None, None => false
    end.

  Definition sender_in_current_prefixb
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) : bool :=
    existsb
      (fun j =>
         bool_decide
           (nth_error (map sender (txsWithHdr (currentBlock (blocks ctx)))) j =
            Some (sender tx)))
      (seq 0 i).

  Definition delundel_in_current_prefixb
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) : bool :=
    existsb
      (fun j =>
         match nth_error
                 (map txAuthoritiesDelFrom (transactions (currentBlock (blocks ctx)))) j
         with
         | Some auths => bool_decide (Some (sender tx) ∈ auths)
         | None => false
         end)
      (seq 0 i).

  Definition tx_seen_within_k (e : ExtraAcStates) (tx : TxWithHdr) : bool :=
    let startIndex := (txBlockNum tx - 2)%N in
    match lastTxInBlockIndex (e (sender tx)) with
    | Some index => asbool ((startIndex <= index)%N /\ (index <= txBlockNum tx)%N)
    | None => false
    end.

  Definition delundel_seen_within_k (e : ExtraAcStates) (tx : TxWithHdr) : bool :=
    let startIndex := (txBlockNum tx - 2)%N in
    match lastDelUndelInBlockIndex (e (sender tx)) with
    | Some index => asbool ((startIndex <= index)%N /\ (index <= txBlockNum tx)%N)
    | None => false
    end.

  Definition historyConsistent (c: MonadChainContext) (e: ExtraAcStates) : Prop :=
    forall i tx,
      nth_error (txsWithHdr (currentBlock (blocks c))) i = Some tx ->
      tx_seen_within_k e tx =
        (sender_in_recent_historyb c tx || sender_in_current_prefixb c i tx)
      /\
      delundel_seen_within_k e tx =
        (delundel_in_recent_historyb c tx || delundel_in_current_prefixb c i tx).
  #[global] Opaque sender_in_block authority_in_block.
  #[global] Opaque sender_in_recent_history delundel_in_recent_history.
  #[global] Opaque sender_in_recent_historyb delundel_in_recent_historyb.
  #[global] Opaque sender_in_current_prefixb delundel_in_current_prefixb.
  #[global] Opaque tx_seen_within_k delundel_seen_within_k.
  #[global] Opaque historyConsistent.
(*    forall addr, configuredReserveBalOfAddr e addr = DefReserve. *)

  Definition cblock (b: MonadChainContext) : Block := currentBlock (blocks b).

  Definition receipt_ty : type := "monad::Receipt"%cpp_type.
  Definition evmc_result_ty : type := "evmc::Result"%cpp_type.

  (** Complete abstract tokens for Monad objects whose methods are outside the
      current proof boundary.  Unlike the former fraction-insensitive wrappers,
      these predicates retain the ownership fraction used by generic library
      representations. *)
  Parameter ReceiptR : Qp -> TxResult -> Rep.
  Parameter EvmcResultR : Qp -> TxResult -> Rep.

  #[global] Declare Instance ReceiptR_cfractional : CFractional1 ReceiptR.
  #[global] Declare Instance EvmcResultR_cfractional :
    CFractional1 EvmcResultR.

  #[global] Instance ReceiptR_as_cfractional : AsCFractional1 ReceiptR.
  Proof. solve_as_cfrac. Qed.

  #[global] Instance EvmcResultR_as_cfractional :
    AsCFractional1 EvmcResultR.
  Proof. solve_as_cfrac. Qed.

  Axiom observeReceiptRType :
    forall q result, Observe (type_ptrR receipt_ty) (ReceiptR q result).
  #[global] Existing Instance observeReceiptRType.

  Axiom observeEvmcResultRType :
    forall q result,
      Observe (type_ptrR evmc_result_ty) (EvmcResultR q result).
  #[global] Existing Instance observeEvmcResultRType.

  Definition observeReceiptRType_F :=
    ltac:(mk_at_obs_fwd observeReceiptRType).
  Definition observeEvmcResultRType_F :=
    ltac:(mk_at_obs_fwd observeEvmcResultRType).

  #[global] Instance receipt_BundledRep :
    concepts.BundledRep receipt_ty TxResult :=
    {| concepts.objR := ReceiptR |}.

  #[global] Instance receipt_outcome_object_value :
    OutcomeObjectValue receipt_ty := {}.

  #[global] Instance evmc_result_BundledRep :
    concepts.BundledRep evmc_result_ty TxResult :=
    {| concepts.objR := EvmcResultR |}.

  #[global] Instance evmc_result_outcome_object_value :
    OutcomeObjectValue evmc_result_ty := {}.

  Definition receipt_vector_ty : type := stdvector receipt_ty.

  #[global] Instance receipt_vector_outcome_object_value :
    OutcomeObjectValue receipt_vector_ty := {}.

  Definition valOfRev (r : Revision) : val := Vint 0. (* TODO: fix *)
  Definition gas_price_model (rev: Z) (tx: Transaction) (base_fee_per_gas: N) : N :=
    gas_price_cpp_model tx base_fee_per_gas.

  (* Bundle of transaction-validation facts used by execute_block for latest Monad
     revision in the dipped_into_reserve proof path. *)
  Definition validTx (tx: TxWithHdr) : Prop :=
    (tx_nonce tx.1.1 < 2 ^ 64 - 1)%N /\
    (tx_gas_limit tx.1.1 < 2 ^ 64)%N /\
    (gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx) < 2 ^ 128)%N /\
    maxTxFee tx =
      (tx_gas_limit tx.1.1 * gas_price_cpp_model tx.1 (tx_base_fee_per_gas tx))%N.

  Record BlockHashBuffer :=
    { fullHistory: list N;
      startIndex: N}.

  Definition lastIndex (b: BlockHashBuffer) : N := startIndex b + lengthN (fullHistory b).

  (* move to utils
  Definition rotate_list {A} (r : Z) (elems : list A) : list A :=
    let sz : Z := length elems in
    let split_count : nat := Z.to_nat $ r `mod` length elems in
    drop split_count elems ++ take split_count elems.
*)  
  Definition BlockHashBufferR (q:Qp) (m: BlockHashBuffer) : Rep :=
    _field "monad::n_" |-> u64R q (lastIndex m).
    (* ** _field "monad::b_" |-> arrayR ... (rotate_list ) *)
  Lemma bhb_split_sn {T} q (b: BlockHashBuffer) (l : list T):
    BlockHashBufferR q b -|- BlockHashBufferR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ l,  (BlockHashBufferR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using. Admitted.

  Lemma bhb_splitl_loopinv {T} q (b: BlockHashBuffer) (l : list T) (i:nat) (p:i=0):
    BlockHashBufferR q b -|- BlockHashBufferR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ (drop i l),  (BlockHashBufferR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using.
    intros. subst. autorewrite with syntactic.
    apply bhb_split_sn.
  Qed.
  
  Lemma header_split_loopinv {T} q (b: BlockHeader) (l : list T) (i:nat) (p:i=0):
    BheaderR q b -|- BheaderR (q/(N_to_Qp (1+ lengthN l))) b ** 
    ([∗ list] _ ∈ (drop i l),  (BheaderR (q*/(N_to_Qp (1+ lengthN l))) b)).
  Proof using. Admitted.

  
Import namemap.
Import translation_unit.
Require Import List.
Import bytestring_core.
Require Import skylabs.auto.cpp.
Require Import skylabs.auto.cpp.specs.


Context  {MODd : exb.source ⊧ CU}.

  Definition txAuthoritires (t: Transaction) : list EIP7702Authority := authorities (t.2).
  
  Definition AuthoritiesR q (auths: list EIP7702Authority) : Rep  :=
    VectorR "std::optional<monad::Address>" (optionAddressR q) q (map del_from auths).

  Definition BlockMetricsR : Rep. Proof. Admitted.

  (* add transaction index to Transaction if not there already *)
  Definition dummyCallTracerR (t: Transaction) : Rep. Proof. Admitted.
  Definition dummyStateTracerR (t: Transaction) : Rep. Proof. Admitted.

  Definition std_span_ty (elt : type) : type :=
    Tnamed
      (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "span"))
         [Atype elt; Avalue (Eint 18446744073709551615%Z Tulong)]).

  Definition std_optional_ty (elt : type) : type :=
    Tnamed
      (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
         [Atype elt]).

  Definition std_allocator_ty (elt : type) : type :=
    Tnamed
      (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "allocator"))
         [Atype elt]).

  Definition std_vector_ty (elt : type) : type :=
    Tnamed
      (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "vector"))
         [Atype elt; Atype (std_allocator_ty elt)]).

  Definition std_default_delete_ty (elt : type) : type :=
    Tnamed
      (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "default_delete"))
         [Atype elt]).

  Definition std_unique_ptr_ty (elt : type) : type :=
    Tnamed
      (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "unique_ptr"))
         [Atype elt; Atype (std_default_delete_ty elt)]).

  Definition std_monostate_ty : type :=
    Tnamed (Nscoped (Nglobal (Nid "std")) (Nid "monostate")).

  Definition trace_state_tracer_ty : type :=
    Tnamed
      (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "variant"))
         ((Apack
            ((Atype std_monostate_ty) ::
             (Atype (Tnamed
               (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "trace"))
                  (Nid "PrestateTracer")))) ::
             (Atype (Tnamed
               (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "trace"))
                  (Nid "StateDiffTracer")))) ::
             (Atype (Tnamed
               (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "trace"))
                  (Nid "AccessListTracer")))) ::
             (Atype (Tnamed
               (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "trace"))
                  (Nid "CodeTracer")))) ::
             nil)) :: nil)).

  Definition execute_block_arg_types (rev : Z) : list type :=
    [Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain"))));
     Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Block"))));
     Qconst (std_span_ty (Qconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Address")))));
     Qconst (std_span_ty
        (Qconst (std_vector_ty
          (std_optional_ty (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Address")))))));
     Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockState")));
     Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHashBuffer"))));
     Tref (Tnamed (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "fiber")) (Nid "FiberGroup")));
     Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockMetrics")));
     Qconst (std_span_ty
        (std_unique_ptr_ty
          (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "CallTracerBase")))));
     Qconst (std_span_ty
        (std_unique_ptr_ty trace_state_tracer_ty));
     Tref trace_state_tracer_ty;
     Tref (Qconst (monad_chain_context_ty rev));
     Qconst Tbool].

  Definition execute_block_transactions_arg_types (rev : Z) : list type :=
    [Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain"))));
     Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHeader"))));
     Qconst (std_span_ty (Qconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction")))));
     Qconst (std_span_ty (Qconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Address")))));
     Qconst (std_span_ty
        (Qconst (std_vector_ty
          (std_optional_ty (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Address")))))));
     Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockState")));
     Tref (Qconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHashBuffer"))));
     Tref (Tnamed (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "fiber")) (Nid "FiberGroup")));
     Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockMetrics")));
     Qconst (std_span_ty
        (std_unique_ptr_ty
          (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "CallTracerBase")))));
     Qconst (std_span_ty
        (std_unique_ptr_ty trace_state_tracer_ty));
     Tref (Qconst (monad_chain_context_ty rev));
     Qconst Tbool].

  (* Obsolete signature, not an assumption of any retained proof. Public main
     adds ExecutionEventRecorder* to execute_block; execute_block.v was already
     outside all.v before the update. See issues/reserve-balance-main-port.md.
  cpp.spec
    (Ninst
       (Nscoped (Nglobal (Nid "monad"))
          (Nfunction function_qualifiers.N "execute_block"
             (execute_block_arg_types 10)))
       [Atype (monad_traits_ty 10)])
    as exbb_spec with (
    \arg{chainp :ptr} "chain" (Vptr chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain

    \arg{blockp: ptr} "block" (Vptr blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block

    \arg{(sendersp: ptr) (qs: Qp)} "senders" (Vptr sendersp)
    \prepost sendersp |-> SpanR "const monad::Address" (addressR qs) qs (map sender (txsWithHdr block)) false
    
    \arg{(authsp: ptr) (qs: Qp)} "authorities" (Vptr authsp)
    \prepost authsp |-> SpanR "const std::vector<std::optional<monad::Address>>" (AuthoritiesR qs) qs (map txAuthoritires (transactions block)) false
    
    \arg{block_statep: ptr} "block_state" (Vptr block_statep)
    \pre{(preBlockState: AugmentedState) g qf}
        block_statep |-> BlockState.Rauth preBlockState g preBlockState
        ** block_statep |-> BlockState.Rfrag preBlockState qf g

    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vptr block_hash_bufferp)
    \prepost{buf qbuf} block_hash_bufferp |-> BlockHashBufferR qbuf buf

    \arg{priority_poolp: ptr} "priority_pool" (Vptr priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool

    \arg{bmetricsp: ptr} "block_metrics" (Vptr bmetricsp)
    \prepost bmetricsp |-> BlockMetricsR
    (** ^ the specs doesnt track the exact metrics: existentially quantified *)
    
    \arg{ctracerp: ptr} "call_tracer" (Vptr ctracerp)
    \prepost ctracerp |-> SpanR "std::unique_ptr<monad::CallTracerBase, std::default_delete<monad::CallTracerBase>>" (dummyCallTracerR) qs (transactions block) false
    
    \arg{stracerp: ptr} "state_tracer" (Vptr stracerp)
    \prepost stracerp |-> SpanR "std::unique_ptr<monad::trace::StateTracer>" (dummyStateTracerR) qs (transactions block) false
    (** ^ the above two args are nop functions in the validator path. they do something in the RPC path, which we ignore. *)

    \arg{system_stracerp: ptr} "system_call_state_tracer"
      (Vptr system_stracerp)
    \prepost{system_stracer_model} system_stracerp |-> dummyStateTracerR system_stracer_model

    \arg{ctxp: ptr} "ctx" (Vptr ctxp)
    \prepost{qctx ctx} ctxp |-> MonadChainContextR qctx ctx

    \arg{trace_transfers: bool} "trace_transfers" (Vbool trace_transfers)
    \pre [| trace_transfers = false |]

    \post{retp}[Vptr retp]
    
       match stateAfterBlockV block preBlockState with
       | Some (actual_final_state, results) =>
           retp |-> OutcomeResultR
             (resultn receipt_vector_ty) receipt_vector_ty outcome_error_ty 1
             (OutcomeValue results)
           ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state
       | None =>
          (* [| ¬ txsFeesUB preBlockState (transactions block) |]  this conjunct can be derived as a lemma about stateAfterBlockV *)
           (Exists error : outcome_status_code,
              retp |-> OutcomeResultR
                (resultn receipt_vector_ty) receipt_vector_ty
                outcome_error_ty 1 (OutcomeError error))
           ** Exists garbage,
                block_statep |-> BlockState.Rauth preBlockState g garbage
       end).
  *)

  (*
Error: cpp.spec: found no matching symbols
*)

(*
  cpp.spec 
  "monad::reset_promises(unsigned long)" as reset_promises with
      ( \with (Transaction: Type)
        \arg{transactions: list Transaction} "n" (Vn (lengthN transactions))
       \pre{newPromisedResource}
           _global "monad::promises" |-> parrayR (Tnamed "boost::fibers::promise<void>") (fun i t => PromiseUnusableR) transactions
       \post Exists prIds, _global "monad::promises" |-> parrayR (Tnamed "boost::fibers::promise<void>") (fun i t => PromiseR (prIds i) (newPromisedResource i t)) transactions).
 *)

  
  (* TODO: this is now the spec of recover_senders, almost.
cpp.spec
  "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)"
  as compute_senders
  with (
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \prepost
        _global "monad::promises" |->
          parrayR
            (Tnamed "boost::fibers::promise<void>")
            (fun i t => PromiseUnusableR)
            (transactions block)
    \pre Exists garbage,
        _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<monad::Address>")
            (fun t=> optionAddressR 1 (garbage t))
            (transactions block)
    \post _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<monad::Address>")
            (fun t=> optionAddressR 1 (Some (sender t)))
            (transactions block)).
*)

Definition execution_result_ty : type := "monad::ExecutionResult"%cpp_type.
Definition resultT := Tnamed (resultn execution_result_ty).
Parameter ExecutionResultR : Qp -> TxResult -> Rep.

#[global] Declare Instance ExecutionResultR_cfractional :
  CFractional1 ExecutionResultR.

#[global] Instance ExecutionResultR_as_cfractional :
  AsCFractional1 ExecutionResultR.
Proof. solve_as_cfrac. Qed.

Axiom observeExecutionResultRType :
  forall q result,
    Observe (type_ptrR execution_result_ty) (ExecutionResultR q result).
#[global] Existing Instance observeExecutionResultRType.

Definition observeExecutionResultRType_F :=
  ltac:(mk_at_obs_fwd observeExecutionResultRType).

#[global] Instance execution_result_BundledRep :
  concepts.BundledRep execution_result_ty TxResult :=
  {| concepts.objR := ExecutionResultR |}.

#[global] Instance execution_result_outcome_object_value :
  OutcomeObjectValue execution_result_ty := {}.

Definition oResultT := (Tnamed (Ninst "std::optional" [Atype resultT])).


(*
Definition nn:= Eval compute in (firstEntryName (findBodyOfFnNamed2 exb.source (isFunctionNamed2 "execute_block_transactions"))).
Print nn.
 *)

  (* Same obsolete recorder-free signature as exbb_spec above.
  cpp.spec
    (Ninst
       (Nscoped (Nglobal (Nid "monad"))
          (Nfunction function_qualifiers.N "execute_block_transactions"
             (execute_block_transactions_arg_types 10)))
       [Atype (monad_traits_ty 10)])
    as exbt_spec with (
    \arg{chainp :ptr} "chain" (Vptr chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain

    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \prepost{qblock block} hdrp |-> BheaderR qblock (header block)

    \arg{txsp: ptr} "transactions" (Vref txsp)
    \prepost txsp |->  SpanR "const ::monad::Transaction" (fun t => TransactionR qblock t) qblock (transactions block) false
    \pre [| 16* lengthN (transactions block) < 2^64 - 1 |]%N
    
    \arg{(sendersp: ptr) (qs: Qp)} "senders" (Vptr sendersp)
    \prepost sendersp |-> SpanR "const monad::Address" (addressR qs) qs (map sender (txsWithHdr block)) false
    
    \arg{(authsp: ptr) (qs: Qp)} "authorities" (Vptr authsp)
    \prepost authsp |-> SpanR "const std::vector<std::optional<monad::Address>>" (AuthoritiesR qs) qs (map txAuthoritires (transactions block)) false
    
    \arg{block_statep: ptr} "block_state" (Vptr block_statep)
    \pre{(preBlockState: AugmentedState) g qf}
        block_statep |-> BlockState.Rauth preBlockState g preBlockState
        ** block_statep |-> BlockState.Rfrag preBlockState qf g

    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vptr block_hash_bufferp)
    \prepost{buf qbuf} block_hash_bufferp |-> BlockHashBufferR qbuf buf

    \arg{priority_poolp: ptr} "priority_pool" (Vptr priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool

    \arg{bmetricsp: ptr} "block_metrics" (Vptr bmetricsp)
    \prepost bmetricsp |-> BlockMetricsR
    (** ^ the specs doesnt track the exact metrics: existentially quantified *)
    
    \arg{ctracerp: ptr} "call_tracer" (Vptr ctracerp)
    \prepost ctracerp |-> SpanR "std::unique_ptr<monad::CallTracerBase, std::default_delete<monad::CallTracerBase>>" (dummyCallTracerR) qs (transactions block) false
    
    \arg{stracerp: ptr} "state_tracer" (Vptr stracerp)
    \prepost stracerp |-> SpanR "std::unique_ptr<monad::trace::StateTracer>" (dummyStateTracerR) qs (transactions block) false
    (** ^ the above two args are nop functions in the validator path. they do something in the RPC path, which we ignore. *)

    \arg{ctxp: ptr} "ctx" (Vptr ctxp)
    \prepost{qctx ctx} ctxp |-> MonadChainContextR qctx ctx

    \arg{trace_transfers: bool} "trace_transfers" (Vbool trace_transfers)
    \pre [| trace_transfers = false |]

    \post{retp}[Vptr retp]
    
       match execTxs  preBlockState (txsWithHdr block) with
       | Some (actual_final_state, results) =>
           retp |-> OutcomeResultR
             (resultn receipt_vector_ty) receipt_vector_ty outcome_error_ty 1
             (OutcomeValue results)
           ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state
       | None =>
           (Exists error : outcome_status_code,
              retp |-> OutcomeResultR
                (resultn receipt_vector_ty) receipt_vector_ty
                outcome_error_ty 1 (OutcomeError error))
           ** Exists garbage,
                block_statep |-> BlockState.Rauth preBlockState g garbage
       end).
  *)


(*
cpp.spec (Ninst "monad::execute_transactions(const monad::Block&, monad::fiber::PriorityPool&, const monad::Chain&, const std::vector<monad::Address, std::allocator<monad::Address>>&, const monad::BlockHashBuffer&, monad::BlockState &)" [Avalue (Eint 11 "enum evmc_revision")]) as exect with (
    \arg{blockp: ptr} "block" (Vref blockp)
    \prepost{qb (block: Block)} blockp |-> BlockR qb block
    \pre [| lengthN (transactions block) < 2^64 - 1 |]%N
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{(sendersp: ptr) (qs: Qp)} "senders" (Vptr sendersp)
    \prepost sendersp |-> VectorR (Tnamed "monad::Address") (addressR qs) qs (map sender (transactions block))
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \prepost{buf qbuf} block_hash_bufferp |-> BlockHashBufferR qbuf buf
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \pre{(preBlockState: StateOfAccounts) g qf}
       block_statep |-> BlockState.Rauth preBlockState g preBlockState
    \prepost block_statep |-> BlockState.Rfrag preBlockState qf g
    \prepost
        _global "monad::promises" |->
          parrayR
            (Tnamed "boost::fibers::promise<void>")
            (fun i t => PromiseUnusableR)
            ((map (fun _ => ()) (transactions block))++[()])
    \pre Exists garbage,
        _global "monad::results" |->
          arrayR
            oResultT
            (fun t=> optional_specs.optionR resultT (fun _ => ResultSuccessR ExecutionResultR) 1$m (garbage t))
            (transactions block)
   \prepost{qs} _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<monad::Address>")
            (fun t=> optionAddressR qs (Some (sender t)))
            (transactions block)
   \post
      let (actual_final_state, receipts) := stateAfterTransactions (header block) preBlockState (transactions block) in
      _global "monad::results" |-> arrayR oResultT (fun r => optional_specs.optionR resultT (fun _ => ResultSuccessR ExecutionResultR) 1$m (Some r)) receipts
      ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state

    ).
    (* \pre assumes that the input is a valid transaction encoding (sender computation will not fail) *)
    cpp.spec "monad::recover_sender(const monad::Transaction&)"  as recover_sender with
        (
    \arg{trp: ptr} "tr" (Vref trp)
    \prepost{qt (tr: Transaction)} trp |-> TransactionR qt tr
    \post{retp} [Vptr retp] retp |-> optionAddressR 1 (Some (sender tr))).
*)    

(*
    cpp.spec (fork_task_nameg "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0") as fork_task with (forkTaskSpec "monad::compute_senders(const monad::Block&, monad::fiber::PriorityPool&)::@0").
 *)
    
    (* redundant: vector subscript spec is generic in stdlib *)
(*
cpp.spec 
  "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::operator[](unsigned long) const" as vector_op_monad with (vector_opg "monad::Transaction").
*)

cpp.spec "std::optional<monad::Address>::operator=(std::optional<monad::Address>&&)" as opt_move_assign with
    (fun (this:ptr) =>
       \arg{other} "other" (Vptr other)
       \pre{oadr} other |-> optionAddressR 1 oadr
       \pre{prev} this |-> optionAddressR 1 prev
       \post [Vptr this] this |-> optionAddressR 1 oadr ** other |-> optionAddressR 1 oadr
    ).

cpp.spec (Nscoped "std::optional<monad::Address>" Ndtor) as destrop with
    (fun (this:ptr) =>
       \pre{oa} this |-> optionAddressR 1 oa
       \post emp
    ).


(*
  erewrite sizeof.size_of_compat;[| eauto; fail| vm_compute; reflexivity].
 *)
Definition txIndex (t: TxWithHdr) : N := indexInBlock t.1.2.

  Definition execute_transaction_spec : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{(tx:TxWithHdr)} "i" (Vn (txIndex tx))
    \pre [| (txIndex tx) < 2^64 - 1 |]%N (* we do i+1 to make the incarnation *)
    \arg{txp} "tx" (Vref txp)
    \prepost{qtx t} txp |-> TransactionR qtx t.1
    \arg{senderp} "sender" (Vref senderp)
    \prepost{qs} senderp |-> addressR qs (sender t)
    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \prepost{qh} hdrp |-> BheaderR qh t.2
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{block_statep: ptr} "block_state" (Vref block_statep)
    \prepost{g qf preBlockState} block_statep |-> BlockState.Rfrag preBlockState qf g
    \arg{prevp: ptr} "prev" (Vref prevp)
    \pre{(prg: gname) (prevTxGlobalState: AugmentedState) (OtherPromisedResources:mpred)}
        prevp |-> PromiseConsumerR prg (OtherPromisedResources ** block_statep |-> BlockState.Rauth preBlockState g prevTxGlobalState)
    \post{retp}[Vptr retp] OtherPromisedResources ** prevp |-> PromiseUnusableR **
    match  execTx prevTxGlobalState t with
    | Some (finalState, result)
      =>
        retp |-> OutcomeResultR
          (resultn execution_result_ty) execution_result_ty outcome_error_ty 1
          (OutcomeValue result)
          ** block_statep |->  BlockState.Rauth preBlockState g finalState
    | None =>
        (Exists error : outcome_status_code,
           retp |-> OutcomeResultR
             (resultn execution_result_ty) execution_result_ty
             outcome_error_ty 1 (OutcomeError error))
        ** Exists garbage,
             block_statep |-> BlockState.Rauth preBlockState g garbage

    end.
    

(*

cpp.spec ((Ninst
             "monad::execute(const monad::Chain&, unsigned long, const monad::Transaction&, const monad::Address&, const monad::BlockHeader&, const monad::BlockHashBuffer&, monad::BlockState&, boost::fibers::promise<void>&)"
             [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))])) as ext1 with (execute_transaction_spec).
 *)
  
#[global] Instance : LearnEq2 ChainR:= ltac:(solve_learnable).
#[global] Instance : LearnEq4 BlockState.Rfrag := ltac:(solve_learnable).
#[global] Instance : LearnEq2 BheaderR := ltac:(solve_learnable).

End with_Sigma.

#[global] Hint Resolve
  observeReceiptRType_F
  observeEvmcResultRType_F
  observeExecutionResultRType_F : sl_opacity.

#[global] Hint Unfold MonadChainContextR : unfold.


Require Import monad.asts.ext.
Require Import Lens.Lens.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}.
  Context {hf: fracG () _Σ}.
  Context  {MODd : ext.source ⊧ CU}.

  (*
  cpp.spec (Nscoped (Nglobal (Nid "monad")) (Nfunction function_qualifiers.N ("get_chain_id") [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain"))))]))
    as get_chain_id with(
      \arg{chainp} "" (Vref chainp)
      \prepost{chain q} chainp |-> ChainR q chain
      \post{retp} [Vptr retp] (retp |-> u256R 1 (chainid chain))).
*)
  Import evm.

      
Let MapOriginalR
           (q: stdpp.numbers.Qp)
           (m: MapModel 
                  evm.address
                  AssumedPreTxAccountState)
  : Rep :=
  AnkerMapR "monad::Address" "monad::OriginalAccountState" 
           addressToN
           addressR
           OriginalAccountStateR
           q
           m.


Definition VersionStack_ty (cppType : type) : type :=
  Tnamed ("monad::VersionStack".<< Atype cppType >>)%cpp_name.

Definition VersionStackSpineR (cppType: type) (q:Qp) (lt:list ptr): Rep. Proof. Admitted.

Definition VersionStackR {ElemType} (cppType: type) (elemRep: Qp -> ElemType -> Rep) (q:Qp) (lt:list (ptr*ElemType)): Rep :=
  VersionStackSpineR cppType q (map fst lt) ** pureR ([∗ list] p ∈ lt, let '(loc, val) := p in  (loc:ptr) |-> elemRep q val).

Let MapCurrentR
           (q: stdpp.numbers.Qp)
           (m: MapModel address (list (ptr* UpdatedAccountState)))
  : Rep :=
  AnkerMapR "monad::Address" "monad::VersionStack<monad::AccountState>" 
           addressToN
           addressR
           (VersionStackR "monad::AccountState" UpdatedAccountStateR)
           q
           m.

Definition StateDirtyStackR (q : Qp) (dirty : list (list evm.address)) : Rep :=
  Exists elts : list (ptr * list evm.address),
    [| map snd elts = dirty |]
    ** deque_specs.DequeR address_set_table_ty address_set_table_allocator_ty
         SenderAuthoritiesSetR q elts.

(*
Definition AnkerMapSliceSpineR {K V:Type} (tykey tyval: type) (khash: K -> N) (* {eqd: EqDecision K} *)
           (krep : Qp -> K -> Rep) 
           (vrep : Qp -> V -> Rep) (* fraction needed as there can be multiple concrrent readers of the value *)
           (* CFrational vrep *)
           (key: K)
           (loc: option ptr)
  : Rep. Proof. Admitted.
 *)

Definition AnkerMapSliceR {K V:Type} `{EqDecision K} (tykey tyval: type) (khash: K -> N) (* {eqd: EqDecision K} *)
           (krep : Qp -> K -> Rep) 
           (vrep : Qp -> V -> Rep) (* fraction needed as there can be multiple concrrent readers of the value *)
           (* CFrational vrep *)
           (qspine: Qp)
           (key: K)
           (val:V)
           map
           (*val: option (ModelWithPtr V)*)
  : Rep := AnkerMapSpineR tykey tyval khash krep qspine map
             ** Exists (i:N),
    match nth_error map (N.to_nat i) with
    | Some (k, loc) => [| k= key |]
                            ** pureR (loc ,, pairSndOffset tykey tyval |-> vrep 1%Qp val)
    | None => False
    end.

      

(*
structR
    "ankerl::unordered_dense::v4_1_0::detail::table<monad::Address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<monad::Address, void>, std::equal_to<monad::Address>, std::allocator<std::pair<monad::Address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"
    (cQp.mut q).
*)

(** TODO: fix: add the actual logs **)
Definition LogsR (q: stdpp.numbers.Qp) : Rep :=
  structR
    "monad::VersionStack<std::vector<monad::Receipt::Log, std::allocator<monad::Receipt::Log>>>"
    (cQp.mut q).

(** 5) Rep for monad::State::code_ (table<bytes32,shared_ptr<CodeAnalysis>>) **)
Definition CodeMapR
           (q: stdpp.numbers.Qp)
           (cm: stdpp.gmap.gmap Corelib.Numbers.BinNums.N (* bytes32 as N *)
                             evm.program)
  : Rep. Proof. Admitted.
(*
  structR
    "ankerl::unordered_dense::v4_1_0::detail::table<monad::bytes32_t, std::shared_ptr<evmone::baseline::CodeAnalysis>, ankerl::unordered_dense::v4_1_0::hash<monad::bytes32_t, void>, std::equal_to<monad::bytes32_t>, std::allocator<std::pair<monad::bytes32_t, std::shared_ptr<evmone::baseline::CodeAnalysis>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"
    (cQp.mut q). *)

(* TODO: more needed *)
Definition isNone {T} (a: option T) := negb (isSome a).

Definition min_balanceN (a: AssumptionExactness) : N :=
  match min_balance a with
  | Some f => f
  | None => 0
  end.

Global Instance lkk {K V} `{Countable K} :
  Lookup K (ModelWithPtr V) (MapModel K V) :=
  fun k m => ((list_to_map m : gmap K (ModelWithPtr V)) !! k).

Definition mapModelLookup {K V} `{Countable K} (m: MapModel K V) (k: K)
  : option (ModelWithPtr V) :=
  ((list_to_map m : gmap K (ModelWithPtr V)) !! k).

Definition initial_assumption_exactness : AssumptionExactness :=
  {| min_balance := Some 0%N; nonce_exact := false |}.

Definition initial_original_account_state
    (acct: option AccountM) : AssumedPreTxAccountState :=
  {| preTxState := acct;
     preTxStorage := storageMapOf acct;
     assumExactness := initial_assumption_exactness |}.

Definition initial_updated_account_state
    (orig: AssumedPreTxAccountState) : UpdatedAccountState :=
  {| postTxState := preTxState orig;
     substateModel := unusedAccountSubstate |}.

Definition state_original_account_state_post
    (orig: MapModel evm.address AssumedPreTxAccountState)
    (addr: evm.address)
    (orig_final: MapModel evm.address AssumedPreTxAccountState)
    (loc: ptr)
    (orig_state: AssumedPreTxAccountState) : Prop :=
  match mapModelLookup orig addr with
  | Some (old_loc, old_state) =>
      orig_final = orig /\ loc = old_loc /\ orig_state = old_state
  | None =>
      exists acct : option AccountM,
        orig_state = initial_original_account_state acct
        /\ orig_final = (addr, (loc, orig_state)) :: orig
  end.

(* TODO inline *)
Definition assumptionOfAddr (s: MapModel evm.address AssumedPreTxAccountState) (a: evm.address)
  : option AssumedPreTxAccountState :=
  match s !! a with
  | None => None
  | Some p =>
          Some (snd p)
  end.

Definition assumptionAndUpdateOfAddr (s: StateM) (a: evm.address)
  : option TxAssumptionsAndUpdates :=
  match preTxAssumedState s !! a with
  | None => None
  | Some p =>
      Some
        {|
          preAssumption := snd p;
          originalLoc := fst p;
          txUpdates :=
            ((newStates s) !! a) ≫=
              (fun a =>
                 match head (snd a) with
                 | None => None
                 | Some (loc, upd) => Some (fst a, (loc, upd))
                 end)
        |}
  end.


Definition validAU (relaxedValidation: bool) (a: option TxAssumptionsAndUpdates)
  : Prop :=
  match option_map preAssumption a with
  | None => True
  | Some assumedPreState =>
      let assumEx := assumExactness assumedPreState in
      match preTxState assumedPreState with
      | None => True
      | Some cs =>
          if isSome (min_balance assumEx)
          then (min_balanceN assumEx <= cs .^ _balance)%N
          else True
      end
  end.

Definition validStateM (a: StateM) : Prop :=
  forall addr,
    validAU (relaxedValidation a) (assumptionAndUpdateOfAddr a addr).

Definition sliceInvariants (au: TxAssumptionsAndUpdates) : Prop :=
  let assumEx := assumExactness (preAssumption au) in
  let assumedPreTxState := preTxState (preAssumption au) in
  match min_balance assumEx, txUpdates au with
  | _, None => True
  | None, _ => True
  | Some minbal, Some (_, (_, txUpds)) =>
      match postTxState txUpds, assumedPreTxState with
      | None, _ => True
      | _, None => True
      | Some csUpdated, Some assumedPre =>
          (balance assumedPre - balance csUpdated <= minbal)%N
      end
  end.

Definition validSliceInvariants (s: StateM) : Prop :=
  forall addr au,
    assumptionAndUpdateOfAddr s addr = Some au ->
    sliceInvariants au.

(* For every address that appears in both maps:
   1) the per-address update stack in newStates must be non-empty; and
   2) if the latest speculative post-state is None, the assumed pre-state
      must also be None. *)
Definition nonEmptyPostStackAndPostNoneImpliesAssumedPreNone (s: StateM) : Prop :=
  forall addr loc tl loc0 aps,
    mapModelLookup (newStates s) addr = Some (loc, tl) ->
    mapModelLookup (preTxAssumedState s) addr = Some (loc0, aps) ->
    match tl with
    | [] => False
    | (_, upd) :: _ => postTxState upd = None -> preTxState aps = None
    end.

(* Backward-compatible name used by existing proofs. *)
Definition validPostNone (s: StateM) : Prop :=
  nonEmptyPostStackAndPostNoneImpliesAssumedPreNone s.

Definition validModel s : Prop :=
  map fst (newStates s) ⊆ map fst (preTxAssumedState s)
  /\ validStateM s
  /\ validPostNone s
  /\ validSliceInvariants s.

Definition ldom {K V} {eqd: EqDecision K} {c: Countable K} (g: gmap K V) := map fst (map_to_list g).

Definition codeMapOfNewStates
  (s : StateM)
  : gmap N evm.program :=
  list_to_map (code_entries_of_state (newStates s)).


Definition codeMapOfPreTxAssumedAccounts
  (s : StateM)
  : gmap N evm.program :=
  list_to_map (code_entries_of_preTxAssumed (preTxAssumedState s)).

(* if any of the maps have an entry, all most have the same value for it *)
Definition consistentMaps (maps: list (gmap N evm.program)) : Prop. Proof using. Admitted.

Definition code_entries_functional (l: list (N * evm.program)) : Prop :=
  forall (h: N) (c1 c2: evm.program),
    (h, c1) ∈ l -> (h, c2) ∈ l -> c1 = c2.

Definition code_entries_nonzero (l: list (N * evm.program)) : Prop :=
  forall (h: N) (c: evm.program),
    (h, c) ∈ l -> h = 0%N -> EVMOpSem.evm.program_length c = 0%Z.

Definition all_code_entries (s : StateM) : list (N * evm.program) :=
  code_entries_of_state (newStates s)
  ++ map_to_list (codeMap s)
  ++ map_to_list (dbBlockStateCodeMapLb s)
  ++ map_to_list (codeMapOfPreTxAssumedAccounts s).

Definition stateCodeMapInvariants s :=
  ldom (codeMapOfNewStates s) ⊆ ldom (dbBlockStateCodeMapLb s) ++ ldom (codeMap s)
  /\ (consistentMaps [codeMap s; (dbBlockStateCodeMapLb s); codeMapOfNewStates s; codeMapOfPreTxAssumedAccounts s])
  /\ (codeMapOfPreTxAssumedAccounts s  ⊆  (dbBlockStateCodeMapLb s))
  /\ code_entries_functional (all_code_entries s)
  /\ code_entries_nonzero (all_code_entries s).

Definition StateCodeMapR (s: StateM) : Rep :=
    _field "monad::State::code_" |-> CodeMapR 1$m%cQp (codeMap s) 
    ** BlockState.CodeMapContainsEntries (blockStateGloc s) (dbBlockStateCodeMapLb s)
    ** [| stateCodeMapInvariants s |].

(** Field-only view of the original-state map. *)
Definition StateOriginalR
    (orig: MapModel evm.address AssumedPreTxAccountState) : Rep :=
  _field "monad::State::original_" |-> MapOriginalR 1$m%cQp orig.

(** Now lay out StateR.  We *no longer* re‐open the section here. **)
  Definition StateR (s: StateM) : Rep := Eval unfold MapOriginalR, MapCurrentR in (
   _field "monad::State::block_state_" |-> refR<"monad::BlockState"> 1$m (blockStatePtr s) ∗
   _field "monad::State::incarnation_" |-> IncarnationR 1$m%cQp (indices s) ∗
   _field "monad::State::original_" |-> MapOriginalR 1$m%cQp (preTxAssumedState s) ∗
   _field "monad::State::current_" |-> MapCurrentR 1$m%cQp (newStates s) ∗
   _field "monad::State::logs_" |-> LogsR 1$m%cQp ∗ (* TOFIX: add a model arg to LogsR *)
   _field "monad::State::version_" |-> uintR 1$m 0 ∗
   _field "monad::State::dirty_" |-> StateDirtyStackR 1$m%cQp [] ∗
   _field "monad::State::relaxed_validation_" |-> boolR 1$m (relaxedValidation s) ∗
   StateCodeMapR s **
   [| validModel s|] **
   structR "monad::State" 1$m).

  cpp.spec "monad::State::original() const"
    as state_original_spec
    with (fun this:ptr =>
      \prepost{st} this |-> StateR st
      \post[Vptr (this ,, _field "monad::State::original_")] emp).

  cpp.spec "monad::State::current() const"
    as state_current_spec
    with (fun this:ptr =>
      \prepost{st} this |-> StateR st
      \post[Vptr (this ,, _field "monad::State::current_")] emp).

  Definition preTxAccountOf (st: StateM) (addr: evm.address) : option AccountM :=
    mapModelLookup (preTxAssumedState st) addr ≫= (fun p => preTxState (snd p)).

  Definition preTxAccountOf_map
      (orig: MapModel evm.address AssumedPreTxAccountState)
      (addr: evm.address) : option AccountM :=
    mapModelLookup orig addr ≫= (fun p => preTxState (snd p)).

  Definition recentAccountOf (st: StateM) (addr: evm.address) : option AccountM :=
    match mapModelLookup (newStates st) addr with
    | Some (_, updates) =>
        match head updates with
        | Some (_, upd) => postTxState upd
        | None => None
        end
    | None => preTxAccountOf st addr
    end.

  Definition state_with_preTxAssumedState
      (st : StateM)
      (orig : MapModel evm.address AssumedPreTxAccountState) : StateM :=
    {| relaxedValidation := relaxedValidation st;
       preTxAssumedState := orig;
       newStates := newStates st;
       blockStatePtr := blockStatePtr st;
       indices := indices st;
       blockStateGloc := blockStateGloc st;
       dbBlockStateCodeMapLb := dbBlockStateCodeMapLb st;
       codeMap := codeMap st |}.

  Definition state_with_preTxAssumedState_and_newStates
      (st : StateM)
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState))) : StateM :=
    {| relaxedValidation := relaxedValidation st;
       preTxAssumedState := orig;
       newStates := cur;
       blockStatePtr := blockStatePtr st;
       indices := indices st;
       blockStateGloc := blockStateGloc st;
       dbBlockStateCodeMapLb := dbBlockStateCodeMapLb st;
       codeMap := codeMap st |}.

  Definition state_original_account_state_block_stateR
      (this : ptr)
      (orig : MapModel evm.address AssumedPreTxAccountState)
      (addr : evm.address) : mpred :=
    match mapModelLookup orig addr with
    | Some _ => emp
    | None =>
        Exists (block_statep : ptr),
        Exists (preBlockState : AugmentedState),
        Exists (g : BlockState.glocs),
          Exists (qblock : Qp),
            this ,, o_field CU "monad::State::block_state_"
              |-> refR<"monad::BlockState"> 1$m block_statep
            ** block_statep |-> BlockState.Rfrag preBlockState qblock g
    end.

  Definition state_recent_account_state_post
      (st : StateM) (addr : evm.address)
      (st_final : StateM) (retp : ptr) (acct : option AccountM) : Prop :=
    match mapModelLookup (newStates st) addr with
    | Some (_, updates) =>
        exists upd_loc upd tl,
          updates = (upd_loc, upd) :: tl
          /\ st_final = st
          /\ retp = upd_loc
          /\ acct = postTxState upd
    | None =>
        exists loc orig_final orig_state,
          state_original_account_state_post
            (preTxAssumedState st) addr orig_final loc orig_state
          /\ st_final = state_with_preTxAssumedState st orig_final
          /\ retp =
               loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState"
                   ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
          /\ acct = preTxState orig_state
    end.

  cpp.spec "monad::State::recent_account_state(const monad::Address&)"
    from state_cpp.source as state_recent_account_state_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \pre{st} this |-> StateR st
      \prepost{preBlockState bs qb}
        blockStatePtr st |-> BlockState.Rfrag preBlockState qb bs
      \post{retp : ptr} [Vref retp]
        Exists st_final,
        Exists acct,
          retp |-> AccountStateRcore 1 acct
          ** (retp |-> AccountStateRcore 1 acct -* this |-> StateR st_final)
          ** [| state_recent_account_state_post st addr st_final retp acct |]
    ).

  Definition replace_current_head_update
      (upd : UpdatedAccountState)
      (updates : list (ptr * UpdatedAccountState))
      : list (ptr * UpdatedAccountState) :=
    match updates with
    | [] => []
    | (upd_loc, _) :: tl => (upd_loc, upd) :: tl
    end.

  Definition replace_current_account_update
      (addr : evm.address)
      (upd : UpdatedAccountState)
      (cur : MapModel evm.address (list (ptr * UpdatedAccountState)))
      : MapModel evm.address (list (ptr * UpdatedAccountState)) :=
    map (fun '(a, (loc, updates)) =>
           if bool_decide (a = addr)
           then (a, (loc, replace_current_head_update upd updates))
           else (a, (loc, updates))) cur.

  Definition state_update_current_account
      (st : StateM) (addr : evm.address) (upd : UpdatedAccountState)
      : StateM :=
    state_with_preTxAssumedState_and_newStates st (preTxAssumedState st)
      (replace_current_account_update addr upd (newStates st)).

  Definition state_current_account_state_post
      (st : StateM) (addr : evm.address)
      (st_final : StateM) (retp : ptr) (upd : UpdatedAccountState) : Prop :=
    match mapModelLookup (newStates st) addr with
    | Some (_, updates) =>
        match updates with
        | (upd_loc, upd0) :: _ =>
            st_final = st
            /\ retp = upd_loc
            /\ upd = upd0
        | [] => False
        end
    | None =>
        exists orig_loc orig_final orig_state cur_loc,
          state_original_account_state_post
            (preTxAssumedState st) addr orig_final orig_loc orig_state
          /\ upd = initial_updated_account_state orig_state
          /\ st_final =
               state_with_preTxAssumedState_and_newStates st orig_final
                 ((addr, (cur_loc, [(retp, upd)])) :: newStates st)
    end.

  cpp.spec "monad::State::current_account_state(const monad::Address&)"
    from state_cpp.source as state_current_account_state_update_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \pre{st} this |-> StateR st
      \prepost{preBlockState bs qb}
        blockStatePtr st |-> BlockState.Rfrag preBlockState qb bs
      \post{retp : ptr} [Vref retp]
        Exists st_final,
        Exists upd,
          retp |-> UpdatedAccountStateR 1 upd
          ** (Forall (F : UpdatedAccountState -> UpdatedAccountState), retp |-> UpdatedAccountStateR 1 (F upd) -*
              this |-> StateR
                (state_update_current_account st_final addr (F upd)))
          ** [| state_current_account_state_post st addr st_final retp upd |]
    ).

  Definition balanceOfAccount (oa: option AccountM) : N :=
    match oa with
    | Some ac => ac .^ _balance
    | None => 0%N
    end.

  Definition account_set_balance (ac : AccountM) (bal : N) : AccountM :=
    (ac &: _coreAc .@ _block_account_balance .= Z_to_w256 (Z.of_N bal))
       &: _balance .= bal.

  Lemma storageMapOf_account_set_balance (ac : AccountM) (bal : N) :
    storageMapOf (Some (account_set_balance ac bal)) =
    storageMapOf (Some ac).
  Proof.
    Admitted.

  Definition account_substate_touch_model
      (m : AccountSubstateModel) : AccountSubstateModel :=
    {| asm_destructed := asm_destructed m;
       asm_touched := true;
       asm_accessed := asm_accessed m;
       asm_accessed_keys := asm_accessed_keys m |}.

  cpp.spec "monad::Account::~Account()"
    from state_cpp.source as account_dtor_spec with (
      fun this : ptr =>
        \pre{acct} this |-> AccountR 1 acct
        \post emp
    ).

  cpp.spec
    "std::numeric_limits<monad::uint256_t>::max()"
    from state_cpp.source as uint256_max_spec with (
      \post{retp : ptr} [Vptr retp]
        retp |-> u256R 1 (2 ^ 256 - 1)
    ).

  cpp.spec "monad::AccountSubstate::touch()"
    from state_cpp.source as account_substate_touch_spec with (
      fun this : ptr =>
        \pre{substate} this |-> AccountSubstateR 1 substate
        \post this |-> AccountSubstateR 1
          (account_substate_touch_model substate)
    ).

  Definition optional_account_has_value_spec : mpred :=
    specify.template.method
      ("std::optional".<<Atype "monad::Account"%cpp_type>>)%cpp_name
      "has_value" function_qualifiers.Nc "bool" [] $
      \this this
      \prepost{acct : option AccountM}
        this |-> optional_specs.optionR
          "monad::Account"%cpp_type AccountR 1 acct
      \post[Vbool (bool_decide (is_Some acct))] emp.

  Definition SpecFor_optional_account_has_value :=
    RegisterSpec optional_account_has_value_spec.
  #[global] Existing Instance SpecFor_optional_account_has_value.

  Definition optional_account_value_spec : mpred :=
    specify.template.method
      ("std::optional".<<Atype "monad::Account"%cpp_type>>)%cpp_name
      "value" function_qualifiers.Nl (Tref "monad::Account"%cpp_type) [] $
      \this this
      \prepost{acct : AccountM}
        this |-> optional_specs.optionR
          "monad::Account"%cpp_type AccountR 1 (Some acct)
      \post[Vptr (this ,, optional_specs.value_offset
                     "monad::Account"%cpp_type)] emp.

  Definition SpecFor_optional_account_value :=
    RegisterSpec optional_account_value_spec.
  #[global] Existing Instance SpecFor_optional_account_value.

  Definition optional_account_arrow_spec : mpred :=
    specify.template.op
      ("std::optional".<<Atype "monad::Account"%cpp_type>>)%cpp_name
      OOArrow function_qualifiers.N (Tptr "monad::Account"%cpp_type) [] $
      \this this
      \prepost{acct : AccountM}
        this |-> optional_specs.optionR
          "monad::Account"%cpp_type AccountR 1
          (Some acct)
      \post[Vptr (this ,, optional_specs.value_offset
                    "monad::Account"%cpp_type)] emp.

  Definition SpecFor_optional_account_arrow :=
    RegisterSpec optional_account_arrow_spec.
  #[global] Existing Instance SpecFor_optional_account_arrow.

  cpp.spec "std::optional<monad::Account>::operator bool() const"
    from state_cpp.source as optional_account_bool_spec with (
      fun this : ptr =>
        \prepost{acct : option AccountM}
          this |-> optional_specs.optionR
            "monad::Account"%cpp_type AccountR 1 acct
        \post[Vbool (bool_decide (is_Some acct))] emp
    ).

  cpp.spec "std::optional<monad::Account>::operator->() const"
    from state_cpp.source as optional_account_arrow_const_spec with (
      fun this : ptr =>
        \prepost{acct : AccountM}
          this |-> optional_specs.optionR
            "monad::Account"%cpp_type AccountR 1
            (Some acct)
        \post[Vptr (this ,, optional_specs.value_offset
                      "monad::Account"%cpp_type)] emp
    ).

  Definition account_add_to_balance_model
      (ac : AccountM) (delta : N) : AccountM :=
    account_set_balance ac (balance ac + delta).

  Definition account_subtract_from_balance_model
      (ac : AccountM) (delta : N) : AccountM :=
    account_set_balance ac (balance ac - delta).

  Definition account_set_nonce_model
      (ac : AccountM) (nonce : Z) : AccountM :=
    ac &: _coreAc .@ _block_account_nonce .= Z_to_w256 nonce.

  Definition updated_account_add_to_balance_model
      (upd : UpdatedAccountState) (ac : AccountM) (delta : N)
      : UpdatedAccountState :=
    {| postTxState := Some (account_add_to_balance_model ac delta);
       substateModel := account_substate_touch_model (substateModel upd) |}.

  Definition updated_account_subtract_from_balance_model
      (upd : UpdatedAccountState) (ac : AccountM) (delta : N)
      : UpdatedAccountState :=
    {| postTxState := Some (account_subtract_from_balance_model ac delta);
       substateModel := account_substate_touch_model (substateModel upd) |}.

  Definition account_storage_write
      (storage : evm.storage) (key value : N) : evm.storage :=
    fun k =>
      if bool_decide (k = bytes32_to_w256 key)
      then bytes32_to_w256 value
      else storage k.

  Definition account_set_storage_model
      (ac : AccountM) (key value : N) : AccountM :=
    {| coreAc :=
         {| block.block_account_address :=
              block.block_account_address (coreAc ac);
            block.block_account_storage :=
              account_storage_write
                (block.block_account_storage (coreAc ac)) key value;
            block.block_account_code :=
              block.block_account_code (coreAc ac);
            block.block_account_balance :=
              block.block_account_balance (coreAc ac);
            block.block_account_nonce :=
              block.block_account_nonce (coreAc ac);
            block.block_account_exists :=
              block.block_account_exists (coreAc ac);
            block.block_account_hascode :=
              block.block_account_hascode (coreAc ac) |};
       incarnation := incarnation ac;
       relevantKeys :=
         key :: filter (fun k => negb (bool_decide (k = key)))
                  (relevantKeys ac);
       balance := balance ac |}.
  
  Definition updated_account_set_nonce_model
      (upd : UpdatedAccountState) (ac : AccountM) (nonce : Z)
      : UpdatedAccountState :=
    {| postTxState := Some (account_set_nonce_model ac nonce);
       substateModel := substateModel upd |}.
(*
  Definition replace_current_head_update
      (upd : UpdatedAccountState)
      (updates : list (ptr * UpdatedAccountState))
      : list (ptr * UpdatedAccountState) :=
    match updates with
    | [] => []
    | (upd_loc, _) :: tl => (upd_loc, upd) :: tl
    end.
*)

  Definition updated_account_set_storage_model
      (upd : UpdatedAccountState) (ac : AccountM) (key value : N)
      : UpdatedAccountState :=
    {| postTxState := Some (account_set_storage_model ac key value);
       substateModel := substateModel upd |}.

  Definition evmc_storage_assigned : Z := 0.
  Definition evmc_storage_added : Z := 1.
  Definition evmc_storage_deleted : Z := 2.
  Definition evmc_storage_modified : Z := 3.
  Definition evmc_storage_deleted_added : Z := 4.
  Definition evmc_storage_modified_deleted : Z := 5.
  Definition evmc_storage_deleted_restored : Z := 6.
  Definition evmc_storage_added_deleted : Z := 7.
  Definition evmc_storage_modified_restored : Z := 8.

  Definition account_state_set_storage_status
      (_ac : AccountM) (_key value original current : N) : Z :=
    if bool_decide (value = 0%N) then
      if bool_decide (current = 0%N) then
        evmc_storage_assigned
      else if bool_decide (original = current) then
        evmc_storage_deleted
      else if bool_decide (original = 0%N) then
        evmc_storage_added_deleted
      else
        evmc_storage_modified_deleted
    else if bool_decide (current = 0%N) then
      if bool_decide (original = 0%N) then
        evmc_storage_added
      else if bool_decide (value = original) then
        evmc_storage_deleted_restored
      else
        evmc_storage_deleted_added
    else if bool_decide (original = current) then
      if bool_decide (original = value) then
        evmc_storage_assigned
      else
        evmc_storage_modified
    else if bool_decide (original = value) then
      evmc_storage_modified_restored
    else
      evmc_storage_assigned.

  Definition account_state_set_storage_post
      (upd : UpdatedAccountState) (ac : AccountM)
      (key value original : N) (status : Z)
      (upd_final : UpdatedAccountState) : Prop :=
    exists current,
      status =
        account_state_set_storage_status ac key value original current /\
      upd_final = updated_account_set_storage_model upd ac key value.

  Definition record_original_storage_read_assumed
      (aps : AssumedPreTxAccountState) (key value : N)
      : AssumedPreTxAccountState :=
    {| preTxState := preTxState aps;
       preTxStorage := immer_map_insert key value (preTxStorage aps);
       assumExactness := assumExactness aps |}.

  Definition record_original_storage_read_map
      (addr : evm.address) (key value : N)
      (orig : MapModel evm.address AssumedPreTxAccountState)
      : MapModel evm.address AssumedPreTxAccountState :=
    map (fun '(addr', (loc, aps)) =>
           if bool_decide (addr' = addr)
           then (addr',
                 (loc, record_original_storage_read_assumed aps key value))
           else (addr', (loc, aps))) orig.

  Definition state_record_original_storage_read
      (st : StateM) (addr : evm.address) (key value : N)
      : StateM :=
    state_with_preTxAssumedState_and_newStates st
      (record_original_storage_read_map addr key value
         (preTxAssumedState st))
      (newStates st).

  Definition current_balance_pessimistic_model (st: StateM) (addr: evm.address) : N :=
    balanceOfAccount (recentAccountOf st addr).

  Definition original_balance_pessimistic_model (st: StateM) (addr: evm.address) : N :=
    balanceOfAccount (preTxAccountOf st addr).

  Definition original_balance_pessimistic_model_map
      (orig: MapModel evm.address AssumedPreTxAccountState)
      (addr: evm.address) : N :=
    balanceOfAccount (preTxAccountOf_map orig addr).

  Definition state_add_to_balance_post
      (st : StateM) (addr : evm.address) (delta : N)
      (st_final : StateM) : Prop :=
    exists st_current retp upd ac,
      state_current_account_state_post st addr st_current retp upd /\
      postTxState upd = Some ac /\
      st_final =
        state_update_current_account st_current addr
          (updated_account_add_to_balance_model upd ac delta).

  Definition state_subtract_from_balance_post
      (st : StateM) (addr : evm.address) (delta : N)
      (st_final : StateM) : Prop :=
    exists st_current retp upd ac,
      state_current_account_state_post st addr st_current retp upd /\
      postTxState upd = Some ac /\
      st_final =
        state_update_current_account
          (update_assum_exactness_state_at st_current addr
             (fun ex =>
                min_balance_update ex
                  (original_balance_pessimistic_model st_current addr)
                  (current_balance_pessimistic_model st_current addr)
                  delta))
         addr
         (updated_account_subtract_from_balance_model upd ac delta).

  Definition state_set_storage_post
      (st : StateM) (addr : evm.address) (key value : N) (status : Z)
      (st_final : StateM) : Prop :=
    exists st_current retp upd ac original upd_final,
      state_current_account_state_post st addr st_current retp upd /\
      postTxState upd = Some ac /\
      account_state_set_storage_post
        upd ac key value original status upd_final /\
      let st_updated := state_update_current_account st_current addr upd_final in
      st_final = st_updated \/
      st_final = state_record_original_storage_read st_updated addr key original.

  Definition state_set_nonce_post
      (st : StateM) (addr : evm.address) (nonce : Z)
      (st_final : StateM) : Prop :=
    exists st_current retp upd ac,
      state_current_account_state_post st addr st_current retp upd /\
      postTxState upd = Some ac /\
      st_final =
        state_update_current_account st_current addr
          (updated_account_set_nonce_model upd ac nonce).

  Definition recentAccountOf_stack (updates: list (ptr * UpdatedAccountState)) : option AccountM :=
    match updates with
    | [] => None
    | (_, upd) :: _ => postTxState upd
    end.

  Definition current_balance_pessimistic_model_stack
      (updates: list (ptr * UpdatedAccountState)) : N :=
    balanceOfAccount (recentAccountOf_stack updates).

  Definition StateCurrentLookupR
      (this: ptr)
      (qcur: Qp)
      (addr: evm.address)
      (cur: MapModel evm.address (list (ptr * UpdatedAccountState))) : mpred :=
    match mapModelLookup cur addr with
    | Some (_, cur_stack) =>
        this ,, o_field CU "monad::State::current_"
          |-> AnkerMapSliceR "monad::Address" "monad::VersionStack<monad::AccountState>"
                addressToN addressR (VersionStackR "monad::AccountState" UpdatedAccountStateR)
                qcur addr cur_stack
                (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
    | None =>
        this ,, o_field CU "monad::State::current_"
          |-> AnkerMapSpineR "monad::Address" "monad::VersionStack<monad::AccountState>"
                addressToN addressR qcur
                (map (fun '(a1, (b0, _)) => (a1, b0)) cur)
    end.

  Definition check_min_balance_recent_account_model
      (cur: MapModel evm.address (list (ptr * UpdatedAccountState)))
      (addr: evm.address)
      (orig_state: AssumedPreTxAccountState) : option AccountM :=
    match mapModelLookup cur addr with
    | Some (_, updates) => recentAccountOf_stack updates
    | None => preTxState orig_state
    end.

  Definition check_min_balance_update_model
      (orig: MapModel evm.address AssumedPreTxAccountState)
      (addr: evm.address)
      (acct: option AccountM)
      (value: N) : MapModel evm.address AssumedPreTxAccountState :=
    update_assum_exactness_at addr
      (fun ex =>
         min_balance_update ex
           (original_balance_pessimistic_model_map orig addr)
           (balanceOfAccount acct)
           value)
      orig.

  Definition original_balance_pessimistic_model_assumed
      (orig_state: AssumedPreTxAccountState) : N :=
    balanceOfAccount (preTxState orig_state).

  Definition update_assum_exactness_assumed
      (f: AssumptionExactness -> AssumptionExactness)
      (aps: AssumedPreTxAccountState) : AssumedPreTxAccountState :=
    {| preTxState := preTxState aps;
       preTxStorage := preTxStorage aps;
       assumExactness := f (assumExactness aps) |}.

  Definition set_min_balance_update_assumed
      (orig_state : AssumedPreTxAccountState)
      (value : N) : AssumedPreTxAccountState :=
    update_assum_exactness_assumed
      (fun ex =>
         match min_balance ex with
         | Some old =>
             {| min_balance := Some (N.max old value);
                nonce_exact := nonce_exact ex |}
         | None => ex
         end) orig_state.

  (*
  cpp.spec "monad::State::check_min_balance(const monad::Address&, const monad::uint256_t&)"
    from state_cpp.source as state_check_min_balance_spec
    with (fun this:ptr =>
      \arg{addrp: ptr} "address" (Vref addrp)
      \arg{valuep: ptr} "value" (Vref valuep)
      \pre{st} this |-> StateR st
      \prepost{preBlockState bs qb}
        blockStatePtr st |-> BlockState.Rfrag preBlockState qb bs
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{(qv : Qp) value} valuep |-> u256R qv$c value
      \pre [| is_Some (mapModelLookup (preTxAssumedState st) addr) |]
      \post{retb: bool} [Vbool retb]
        let cur := current_balance_pessimistic_model st addr in
        let orig := original_balance_pessimistic_model st addr in
        let ok := check_min_balance_ok cur value in
        this |-> StateR
          (update_assum_exactness_state_at st addr
             (fun ex => min_balance_update ex orig cur value))
        ** [| retb = ok |]
    ).
  *)

  (* Suspended: this C++ helper was removed on main.
     See issues/reserve-balance-main-port.md; do not register its old contract.
  cpp.spec "monad::State::check_min_balance(const monad::Address&, const monad::uint256_t&)"
    from state_cpp.source as state_check_min_balance_slice_spec
    with (fun this:ptr =>
      \arg{addrp: ptr} "address" (Vref addrp)
      \arg{valuep: ptr} "value" (Vref valuep)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{(qv : Qp) value} valuep |-> u256R qv$c value
      \pre{orig}
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                addressR OriginalAccountStateR 1 orig
      \pre
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                addressToN addressR 1
                (map (λ '(a1, (b0, _)), (a1, b0)) orig)
      \prepost{preBlockState bs qb (bsp: ptr)}
        this ,, o_field CU "monad::State::block_state_"
          |-> refR<"monad::BlockState"> 1$m bsp
        ** bsp |-> BlockState.Rfrag preBlockState qb bs
      \prepost{qcur cur}
        StateCurrentLookupR this qcur addr cur
      \pre [|
        match mapModelLookup cur addr with
        | Some _ => is_Some (mapModelLookup orig addr)
        | None => True
        end |]
      \prepost this |-> structR "monad::State" 1$m
      \post{retb: bool} [Vbool retb]
        [|
          match mapModelLookup cur addr with
          | Some (_, cur_stack) =>
              retb =
              check_min_balance_ok
                (current_balance_pessimistic_model_stack cur_stack)
                value
          | None => True
          end |]
        **
        Exists (orig_final : MapModel evm.address AssumedPreTxAccountState),
        Exists (loc : ptr),
        Exists (orig_state : AssumedPreTxAccountState),
        Exists (acct : option AccountM),
          this ,, o_field CU "monad::State::original_"
               |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                     addressR OriginalAccountStateR 1
                     (check_min_balance_update_model orig_final addr acct value)
          ** this ,, o_field CU "monad::State::original_"
               |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                     addressToN addressR 1
                     (map (fun '(a1, (b0, _)) => (a1, b0))
                        (check_min_balance_update_model orig_final addr acct value))
          ** [| state_original_account_state_post
                 orig addr orig_final loc orig_state |]
          ** [| acct = check_min_balance_recent_account_model cur addr orig_state |]
          ** [| retb = check_min_balance_ok (balanceOfAccount acct) value |]
    ).
  *)

  (*
  cpp.spec "monad::State::check_min_balance(const monad::Address&, const monad::uint256_t&)"
    from state_cpp.source as state_check_min_balance_borrowed_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \arg{valuep : ptr} "value" (Vref valuep)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{qv value} valuep |-> u256R qv value
      \pre{(st : StateM) (retp : ptr) (upd : UpdatedAccountState)
            (ac : AccountM) (F : UpdatedAccountState -> UpdatedAccountState)}
        retp |-> UpdatedAccountStateR 1 upd
      \pre
        (retp |-> UpdatedAccountStateR 1 (F upd) -*
          this |-> StateR
            (state_update_current_account st addr (F upd)))
      \pre [| postTxState upd = Some ac |]
      \pre [| (value <= balance ac)%N |]
      \post [Vbool true]
        retp |-> UpdatedAccountStateR 1 upd
        ** (retp |-> UpdatedAccountStateR 1 (F upd) -*
          this |-> StateR
            (state_update_current_account
               (update_assum_exactness_state_at st addr
                  (fun ex =>
                     min_balance_update ex
                       (original_balance_pessimistic_model st addr)
                       (current_balance_pessimistic_model st addr)
                       value))
               addr (F upd)))
*)
  cpp.spec "monad::State::set_nonce(const monad::Address&, unsigned long)"
    from state_cpp.source as state_set_nonce_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \arg{nonce : Z} "nonce" (Vint nonce)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \pre{st} this |-> StateR st
      \prepost{preBlockState bs qb}
        blockStatePtr st |-> BlockState.Rfrag preBlockState qb bs
      \pre [| (0 <= nonce < 2 ^ 64)%Z |]
      \pre [|
        exists ac,
          recentAccountOf st addr = Some ac |]
      \post
        Exists st_final,
          this |-> StateR st_final
          ** [| state_set_nonce_post st addr nonce st_final |]
    ).

  cpp.spec "monad::State::add_to_balance(const monad::Address&, const monad::uint256_t&)"
    from state_cpp.source as state_add_to_balance_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \arg{deltap : ptr} "delta" (Vref deltap)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{qdelta delta} deltap |-> u256R qdelta delta
      \pre{st} this |-> StateR st
      \prepost{preBlockState bs qb}
        blockStatePtr st |-> BlockState.Rfrag preBlockState qb bs
      \pre [|
        exists ac,
          recentAccountOf st addr = Some ac /\
          (balance ac + delta < 2 ^ 256)%N |]
      \post
        Exists st_final,
          this |-> StateR st_final
          ** [| state_add_to_balance_post st addr delta st_final |]
    ).

  cpp.spec "monad::State::subtract_from_balance(const monad::Address&, const monad::uint256_t&)"
    from state_cpp.source as state_subtract_from_balance_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \arg{deltap : ptr} "delta" (Vref deltap)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{qdelta delta} deltap |-> u256R qdelta delta
      \pre{st} this |-> StateR st
      \prepost{preBlockState bs qb}
        blockStatePtr st |-> BlockState.Rfrag preBlockState qb bs
      \pre [|
        exists ac,
          recentAccountOf st addr = Some ac /\
          (delta <= balance ac)%N /\
          (balance ac < 2 ^ 256)%N |]
      \post
        Exists st_final,
          this |-> StateR st_final
          ** [| state_subtract_from_balance_post st addr delta st_final |]
    ).

  #[local] Instance evmc_storage_status_type_compat :
    type_compat.TypeCompat "enum evmc_storage_status" Vint := {}.

  cpp.spec "monad::AccountState::set_storage(const monad::bytes32_t&, const monad::bytes32_t&, const monad::bytes32_t&)"
    from state_cpp.source as account_state_set_storage_spec
    with (fun this : ptr =>
      \arg{keyp : ptr} "key" (Vref keyp)
      \arg{valuep : ptr} "value" (Vref valuep)
      \arg{originalp : ptr} "original_value" (Vref originalp)
      \prepost{qkey key} keyp |-> bytes32R qkey key
      \prepost{qvalue value} valuep |-> bytes32R qvalue value
      \prepost{qorig original} originalp |-> bytes32R qorig original
      \pre{upd ac}
        this |-> UpdatedAccountStateR 1 upd
        ** [| postTxState upd = Some ac |]
      \post{status : Z} [Vint status]
        Exists upd_final,
          this |-> UpdatedAccountStateR 1 upd_final
          ** [| account_state_set_storage_post
                 upd ac key value original status upd_final |]
    ).

  cpp.spec "monad::State::set_storage(const monad::Address&, const monad::bytes32_t&, const monad::bytes32_t&)"
    from state_cpp.source as state_set_storage_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \arg{keyp : ptr} "key" (Vref keyp)
      \arg{valuep : ptr} "value" (Vref valuep)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{qkey key} keyp |-> bytes32R qkey key
      \prepost{qvalue value} valuep |-> bytes32R qvalue value
      \pre{st} this |-> StateR st
      \prepost{preBlockState bs qb}
        blockStatePtr st |-> BlockState.Rfrag preBlockState qb bs
      \pre [| exists ac, recentAccountOf st addr = Some ac |]
      \post{status : Z} [Vint status]
        Exists st_current retp upd ac original upd_final,
        Exists st_final,
          this |-> StateR st_final
          ** [| state_current_account_state_post st addr st_current retp upd |]
          ** [| postTxState upd = Some ac |]
          ** [| account_state_set_storage_post
                 upd ac key value original status upd_final |]
          ** [| state_set_storage_post st addr key value status
                 st_final |]
    ).

  cpp.spec "monad::State::get_balance(const monad::Address&)"
    from state_cpp.source as state_get_current_balance_pessimistic_spec
    with (fun this:ptr =>
      \arg{addrp: ptr} "address" (Vref addrp)
      \prepost{st} this |-> StateR st
      \prepost{q addr} addrp |-> addressR q addr
      \post{retp: ptr} [Vptr retp]
        retp |-> bytes32R 1 (current_balance_pessimistic_model st addr)
    ).

  cpp.spec "monad::State::get_original_balance(const monad::Address&)"
    from state_cpp.source as state_get_original_balance_pessimistic_spec
    with (fun this:ptr =>
      \arg{addrp: ptr} "address" (Vref addrp)
      \pre{orig}
        this |-> StateOriginalR orig
      \prepost{q addr} addrp |-> addressR q addr
      \pre [| is_Some (mapModelLookup orig addr) |]
      \post{retp: ptr} [Vptr retp]
        retp |-> u256R 1 (original_balance_pessimistic_model_map orig addr)
        ** [| (original_balance_pessimistic_model_map orig addr < 2 ^ 256)%N |]
        ** this |-> StateOriginalR (update_assum_exactness_at addr exact_balance_update orig)
    ).

  Definition code_piece_qp : Qp := (1 / N_to_Qp (2 ^ 32)%N)%Qp.
  Definition VarCodeR (q: Qp) (code: evm.program ) : Rep. Proof. Admitted.
  Definition intercode_piece_qp : Qp := (1 / N_to_Qp (2 ^ 32)%N)%Qp.
  Definition IntercodeR (q: Qp) (code: evm.program) : Rep. Proof. Admitted.

  (* Look in new-state code first, then pre-tx assumed accounts, then DB/BlockState lower bound. *)
  Definition read_code_program
      (st: StateM) (hash: N) : option evm.program :=
    match codeMapOfNewStates st !! hash with
    | Some code => Some code
    | None =>
        match codeMapOfPreTxAssumedAccounts st !! hash with
        | Some code => Some code
        | None => dbBlockStateCodeMapLb st !! hash
        end
    end.

  (*
  Definition state_is_delegated_model
      (st: StateM) (codeMapLb: gmap N evm.program) (hash: N) : bool :=
    if (hash =? 0)%N then false else
      match computeCodeMap st !! hash with
      | Some code => isDelegationMarker code
      | None =>
          match codeMapLb !! hash with
          | Some code => isDelegationMarker code
          | None => false
          end
      end.
   *)

  cpp.spec "monad::State::read_code(const monad::bytes32_t&)"
    from state_cpp.source as state_read_code_spec
    with (fun this:ptr =>
      \arg{hashp: ptr} "code_hash" (Vref hashp)
      \prepost{st} this |-> StateCodeMapR st
      \prepost this |-> structR "monad::State" 1
      \prepost{qhash hash} hashp |-> bytes32R (cQp.mut qhash) hash
      \pre{code} [| read_code_program st hash = Some code |]
      \post{retp: ptr} [Vptr retp]
        Exists (ctrlid: CtrlBlockId) (owned: ptr),
            retp |-> @SharedPtrR _ _ _ _ (Tnamed "monad::vm::Varcode") ctrlid
              (fun _ => VarCodeR code_piece_qp
                code) owned
    ).

  (* Removed C++ helper; see issues/reserve-balance-main-port.md.
  cpp.spec "monad::State::is_delegated(const monad::bytes32_t&)"
    from state_cpp.source as state_is_delegated_spec2
    with (fun this:ptr =>
      \arg{hashp: ptr} "code_hash" (Vref hashp)
      \prepost{st} this |-> StateCodeMapR st
      \prepost this |-> structR "monad::State" 1
      \prepost{(qhash : Qp) hash} hashp |-> bytes32R qhash$c hash
      \pre{code} [| read_code_program st hash = Some code |]
      \post{retb: bool} [Vbool retb] [| retb = isDelegationMarker code |]
         ).
  *)
  (*
  cpp.spec "monad::State::is_delegated(const monad::bytes32_t&)"
    from state_cpp.source as state_is_delegated_spec
    with (fun this:ptr =>
      \arg{hashp: ptr} "code_hash" (Vref hashp)
      \prepost{st} this |-> StateR st
      \prepost{qhash hash} hashp |-> bytes32R (cQp.mut qhash) hash
      \prepost{preBlockState g qf codeMapLowerBound}
        (blockStatePtr st) |-> BlockState.Rfrag preBlockState qf g codeMapLowerBound
      \post{retb: bool} [Vbool retb]
        [| retb = state_is_delegated_model st codeMapLowerBound hash |]
    ).
 *)
  #[global] Instance evmc_revision_type_compat :
    TypeCompat "enum evmc_revision" Vint := {}.

  #[global] Instance monad_revision_type_compat :
    TypeCompat "enum monad_revision" Vint := {}.

  Section monad_traits_specs.
    Context (rev: Z).

    Definition monad_traits_monad_rev_spec :=
      specify
        {|
          info_name :=
            (("monad::MonadTraits" .<< Avalue (Eint rev "enum monad_revision") >>)%cpp_name
               .:: Nfunction function_qualifiers.N "monad_rev" []);
          info_type := tFunction "enum monad_revision"%cpp_type []
        |} (
        \post[Vint rev] emp
        ).

    Definition SpecFor_monad_traits_monad_rev :=
      RegisterSpec monad_traits_monad_rev_spec.
    #[global] Existing Instance SpecFor_monad_traits_monad_rev.

    Definition gas_price_traits_spec :=
      specify
        {|
          info_name :=
            ("monad::gas_price(const monad::Transaction&, const monad::uint256_t&)"
               .<< Atype
                     (Tnamed
                        ("monad::MonadTraits" .<< Avalue (Eint rev "enum monad_revision") >>))
               >>);
          info_type :=
            tFunction u256t
              [Tref (Tconst (Tnamed "monad::Transaction"));
               Tref (Tconst u256t)]
        |} (
        \arg{txp: ptr} "tx" (Vref txp)
        \prepost{qtx tx} txp |-> TransactionR qtx tx
        \arg{basefeep: ptr} "base_fee_per_gas" (Vref basefeep)
        \prepost{qfee base_fee} basefeep |-> u256R qfee base_fee
        \post{retp: ptr} [Vptr retp]
          retp |-> u256R 1 (gas_price_model rev tx base_fee)
        ).

    Definition SpecFor_gas_price_traits := RegisterSpec gas_price_traits_spec.
    #[global] Existing Instance SpecFor_gas_price_traits.
  End monad_traits_specs.

  Definition nullifyBalNonceStorage (e: AccountM) : AccountM. Proof. Admitted.
  (*    := {[ e with evm.account_balance := 0, evm.account_nonce:=0 ]}. *)
  
  (*
  Definition preImpl2 (blockStatePtr: ptr) (senderAddr: evm.address) (sender: account_state): StateM:=
    {|
      blockStatePtr:= blockStatePtr;
      newStates:= ∅;
      original := <[senderAddr := sender]>∅;
    |}. *)
(*
  Definition EvmcResultR (r: TxResult): Rep. Proof. Admitted. *)

  Open Scope Z_scope.

  Definition zbvfun (fz: Z -> Z) (w: keccak.w256): keccak.w256:=
    let wnz := fz (w256_to_Z w) in
    Z_to_w256 wnz.
    
   
  Definition zbvlens {A:Type} (l: Lens A A keccak.w256 keccak.w256): Lens A A Z Z :=
    {| view := λ a : A, w256_to_Z (a .^ l);
      over := λ (fz : Z → Z) (a : A), (l %= zbvfun fz) a |}.
  Locate _balance.
  (*
  Definition _balance : Lens AccountM AccountM Z Z (* TODO: Z -> N *):=
    zbvlens (_coreAc .@ _block_account_balance).
*)
  Definition _nonce : Lens AccountM evm.account_state Z Z:=
    zbvlens (_coreAc .@ _block_account_nonce).

  Definition _storage (key: Z): Lens AccountM evm.account_state Z Z:=
    zbvlens (_coreAc .@ _block_account_storage .@ (ix (Z_to_w256 key))).
  
  Definition satAccountNonStorageAssumptions (relaxedValidation: bool) (a: option AssumedPreTxAccountState) (actualPreTxAcState: option AccountM) : Prop :=
      match  a  with
      | Some assumedPre =>
          let assumEx := assumExactness assumedPre in
          match preTxState assumedPre, actualPreTxAcState  with
          | Some cs, Some csActual =>
             (let bal_exact := cs .^ _balance = csActual .^ _balance in
              let bal_min_ok :=
                if isSome (min_balance assumEx)
                then (min_balanceN assumEx <= csActual .^ _balance)%N
                else True in
              if negb relaxedValidation
              then bal_exact /\ bal_min_ok
              else if isNone (min_balance assumEx)
                   then bal_exact
                   else bal_min_ok)
             /\ (if (negb relaxedValidation || nonce_exact assumEx)
                 then cs .^ _nonce = (csActual).^ _nonce
                 else True)
          | None, None => True
          | _, _ => False
          end
      | None  => True
      end.

  Definition satAccountStrageAssumptions (relaxedValidation: bool) (a: option AssumedPreTxAccountState) (actualPreTxAcState: option AccountM) : Prop :=
      match  a  with
      | Some assumedPreState =>
          let assumEx := assumExactness assumedPreState in
          match preTxState assumedPreState, actualPreTxAcState  with
          | Some cs, Some csActual =>
             account_code csActual = account_code cs
             /\ (forall storageKey: N, storageKey ∈ relevantKeys cs
                                       -> csActual .^ _storage storageKey = cs .^ _storage storageKey)
          | None, None => True
          | _, _ => False
          end
      | None  => True
      end.
  
  
  Definition satAccountAssumptions (relaxedValidation: bool) (a: option AssumedPreTxAccountState) (actualPreTxAcState: option AccountM) : Prop :=
    satAccountNonStorageAssumptions relaxedValidation a actualPreTxAcState /\  satAccountStrageAssumptions relaxedValidation a actualPreTxAcState.

  Definition satisfiesAssumptions' (relaxed : bool) (a: MapModel evm.address AssumedPreTxAccountState) (preTxState: StateOfAccounts) : Prop :=
    forall acAddr: address,
      satAccountAssumptions relaxed (assumptionOfAddr a acAddr) (Some (preTxState acAddr)).

  Definition satisfiesAssumptions (a: StateM) (preTxState: StateOfAccounts) : Prop :=
    satisfiesAssumptions' (relaxedValidation a)  (preTxAssumedState a) preTxState.
  
  
  Definition dummyEx : AssumptionExactness :=  {| min_balance := None; nonce_exact := true |}.

  Definition postTxActualBalNonce (assumedPreTxState : account_state) (assumEx: AssumptionExactness)  (speculativePostTxState: account_state)  (actualPreTxState: account_state) : (Z*Z) :=
        (actualPreTxState .^ _balance + (speculativePostTxState .^ _balance - assumedPreTxState .^ _balance),
         actualPreTxState  .^ _nonce + (speculativePostTxState .^ _nonce - assumedPreTxState .^ _nonce)).

  Definition dummyInc: Indices := {| block_index :=0; tx_index :=0 |}.
  (*
  Global Instance: LookupTotal address account_state StateOfAccounts :=
    fun a s => match s !! a with
               | Some f => f
               | None => dummyAc
               end.
*)
(*
  Definition applyUpdates (p: PartialAccountState) (base: AccountM) : AccountM :=
    {
 *)

  
  Definition updateStorage (pre: option evm.storage) (updates: option AccountM) : evm.storage. Proof. Admitted.
  Definition accountFinalVal (relaxedValidation: bool) (au : TxAssumptionsAndUpdates) (actualPreTxState: option AccountM)  : option AccountM :=
    let assumEx := assumExactness (preAssumption au) in
    match  txUpdates au   with
    | None => actualPreTxState
    | Some (_, (_,txUpds)) =>
        match postTxState txUpds  with
        | None => None (* account did suicide if it existed *)
        | Some csUpdated =>
            let base := csUpdated &: _coreAc .@ _block_account_storage .= updateStorage (option_map (block.block_account_storage ∘ coreAc) actualPreTxState) (Some csUpdated) in
            if relaxedValidation then
              match preTxState (preAssumption au), actualPreTxState  with
              | Some csAssumed, Some csActual =>
                let assumEx := assumExactness (preAssumption au) in
                  Some(
                  let '(postTxBal, postTxNonce) := postTxActualBalNonce csAssumed assumEx csUpdated csActual in
                  let postAcState := if (isNone (min_balance assumEx)) then base else base &: _balance .= Z.to_N postTxBal in
                  if (nonce_exact assumEx) then postAcState else (postAcState &: _nonce .= postTxNonce))
              | _ , _ => Some base (* no relexed validation if either account is dead *)
              end
            else Some base
        end
    end.
        


  Definition gmapMap {K V} `{Countable K} (f: K -> V -> option V) (g: gmap K V) : gmap K V. Proof. Admitted.
  (*  Definition del {K V} `{Countable K} (k:K) (g: gmap K V) : gmap K V := delete k g. *)

  Definition applyUpdates (m: StateM) (preTxState: StateOfAccounts) :StateOfAccounts :=
    fun addr =>
      match assumptionAndUpdateOfAddr m addr with
      | None => preTxState addr
      | Some au =>
          match accountFinalVal (relaxedValidation m) au (Some (preTxState addr)) with
          | None =>  dummyAc
          | Some fv =>   fv
          end
      end.

  (*
  Definition applyUpdates (m: StateM) (preTxState: AugmentedState) : AugmentedState :=
    (applyUpdates' m preTxState.1 , preTxState.2).
    *)  
  (*
  Definition execute_impl2_spec : WpSpec mpredI val val :=
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{txp} "tx" (Vref txp)
    \prepost{qtx t} txp |-> TransactionR qtx t
    \arg{senderp} "sender" (Vref senderp)
    \prepost{qs} senderp |-> addressR qs (sender t)
    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \prepost{qh header} hdrp |-> BheaderR qh header
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{statep: ptr} "state" (Vref statep)
    \pre{au: StateM} statep |-> StateR au
    \pre [| newStates au = []|] (* this is a weaker asumption than the impl, which also guarantees that preTxAssumedState only has the sender's account *)
    \prepost{(preBlockState: StateOfAccounts) (gl: BlockState.glocs) qb}
      (blockStatePtr au) |-> BlockState.Rfrag preBlockState qb gl
    \post{retp}[Vptr retp] Exists assumptionsAndUpdates result,
      statep |-> StateR assumptionsAndUpdates
      ** retp |-> OutcomeResultR
           (resultn evmc_result_ty) evmc_result_ty outcome_error_ty 1
           (OutcomeValue result)
       ** [| blockStatePtr assumptionsAndUpdates = blockStatePtr au |]
       ** [| indices assumptionsAndUpdates = indices au |]
      ** [| forall preTxState,
            satisfiesAssumptions assumptionsAndUpdates preTxState -> 
            let '(postTxState, actualResult) := stateAfterTransactionAux header preTxState (N.to_nat (tx_index (indices au))) t in
            postTxState = applyUpdates assumptionsAndUpdates preTxState /\ result = actualResult |].
   *)

  Definition execute_impl2_specg : WpSpec mpredI val val :=
    \with (speculative: bool) (* making this the first argument helps in proofs *)
     \arg{ctracerp} "" (Vref ctracerp)
    \arg{chainp :ptr} "chain" (Vref chainp)
    \prepost{(qchain:Qp) (chain: Chain)} chainp |-> ChainR qchain chain
    \arg{txp} "tx" (Vref txp)
    \prepost{qtx (t: TxWithHdr)} txp |-> TransactionR qtx t.1
    \arg{senderp} "sender" (Vref senderp)
    \prepost{qs} senderp |-> addressR qs (sender t)
    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \prepost{qh} hdrp |-> BheaderR qh t.2
    \arg{block_hash_bufferp: ptr} "block_hash_buffer" (Vref block_hash_bufferp)
    \arg{statep: ptr} "state" (Vref statep)
    \pre{au: StateM} statep |-> StateR au
    \pre [| newStates au = []|] (* this is a weaker asumption than the impl, which also guarantees that preTxAssumedState only has the sender's account *)
    \pre [| indices au = Build_Indices (txBlockNum t) (txIndex t) |]
    \prepost{(preBlockState: AugmentedState) (gl: BlockState.glocs) qb}
    (blockStatePtr au) |-> BlockState.Rfrag preBlockState qb gl
    \prepost{preTxState} (if speculative then emp else blockStatePtr au |-> BlockState.Rauth preBlockState gl preTxState)
    \post{retp}[Vptr retp] Exists assumptionsAndUpdates result,
      statep |-> StateR assumptionsAndUpdates
      ** retp |-> OutcomeResultR
           (resultn evmc_result_ty) evmc_result_ty outcome_error_ty 1
           (OutcomeValue result)
      ** [| blockStatePtr assumptionsAndUpdates = blockStatePtr au |]
      ** [| validStateM assumptionsAndUpdates |]
       ** [| indices assumptionsAndUpdates = indices au |]
       ** [| let postCond (preTxState : StateOfAccounts) :=
               let 'Build_EvmExecResult postTxState actualResult changed execAccounts := execTxCore' preTxState t in
               postTxState = applyUpdates assumptionsAndUpdates preTxState /\ result = actualResult in
             if speculative then 
               forall preTxState, satisfiesAssumptions assumptionsAndUpdates preTxState -> postCond preTxState
             else satisfiesAssumptions assumptionsAndUpdates preTxState.1 /\ postCond preTxState.1
          |].


  cpp.spec "monad::BlockState::can_merge(monad::State&) const"
    as can_merge with ( fun (this:ptr) =>
     \arg{statep} "state" (Vptr statep) 
     \prepost{assumptionsAndUpdates} statep |-> StateR assumptionsAndUpdates
     \prepost{preBlockState invId preTxState} this |-> BlockState.Rauth preBlockState invId preTxState
     \post{b} [Vbool b] [| if b
                           then satisfiesAssumptions assumptionsAndUpdates preTxState.1
                           else Logic.True |]).

  cpp.spec "monad::BlockState::merge(const monad::State&)"
    as merge with (fun (this:ptr) =>
    \arg{statep} "state" (Vptr statep) 
    \prepost{assumptionsAndUpdates} statep |-> StateR assumptionsAndUpdates
    \pre{preBlockState invId preTxState} this |-> BlockState.Rauth preBlockState invId preTxState
    \pre [| satisfiesAssumptions assumptionsAndUpdates preTxState.1 |]
    \post this |-> BlockState.Rauth preBlockState invId (applyUpdates assumptionsAndUpdates preTxState.1, preTxState.2)).

  (* The shared read may materialize a DB value into BlockState's synchronized
     cache, but callers only rely on receiving some account snapshot. *)
  cpp.spec "monad::BlockState::read_account(const monad::Address&)"
    from state_cpp.source as block_state_read_account_frag_spec with (fun (this:ptr) =>
      \arg{addressp} "address" (Vref addressp)
      \prepost{preBlockState g qblock} this |-> BlockState.Rfrag preBlockState qblock g
      \prepost{qaddr address} addressp |-> addressR qaddr address
      \post{retp:ptr} [Vptr retp]
        Exists (acct : option AccountM),
          retp |-> optional_specs.optionR
            "monad::Account" AccountR 1 acct
    ).

  (* spec for speculative phase *)
  cpp.spec "monad::BlockState::read_storage(const monad::Address&, monad::Incarnation, const monad::bytes32_t&)"
    from state_cpp.source as read_storage_spec with (fun (this:ptr) =>
      \arg{addressp} "address" (Vref addressp)
      \arg{incp} "incarnation" (Vptr incp)
      \arg{keyp} "key" (Vref keyp)
      \prepost{preBlockState g qblock}
        this |-> BlockState.Rfrag preBlockState qblock g
      \prepost{qaddr address} addressp |-> addressR qaddr address
      \prepost{qinc indices} incp |-> IncarnationR qinc indices
      \prepost{qkey key} keyp |-> bytes32R qkey key
      \post{retp:ptr} [Vptr retp] Exists anyvalue:N, retp |-> bytes32R 1 anyvalue). 

  Definition lookupStorage (s: StateOfAccounts) (addr: address) (key: N) (blockTxInd: Indices) : N. Proof. Admitted.

(* TODO: add spec of read_storage *)

(*
  Definition StateConstr : ptr -> WpSpec mpredI val val :=
    fun (this:ptr) =>
      \arg{bsp} "" (Vref bsp)
      \arg{incp} "" (Vptr incp)
      \pre{q inc} incp |-> IncarnationR q inc 
      \post this |-> StateR {| blockStatePtr := bsp; indices:= inc; preTxAssumedState := []; newStates:= []; relaxedValidation := false; dbBlockStateCodeMapLb := ∅ |}.
 *)
  
  Definition WithdrawalR (q: cQp.t) (w: Withdrawal) : Rep. Proof. Admitted.
  Definition ConsensusBlockHeaderR (q: cQp.t) (w: ConsensusBlockHeader) : Rep. Proof. Admitted.
  Definition EmptyCallFramesR (q: cQp.t) : Rep. Proof. Admitted.

  Definition recent_spec_core : ptr -> WpSpec mpredI val val  := (fun (this: ptr) =>
                \prepost{q h tl} this |-> VersionStackSpineR
                  "monad::AccountState"
                     (cQp.mut q)
                     (h::tl)
                     \post [Vptr  h] emp).
  cpp.spec "monad::VersionStack<monad::AccountState>::recent()"
      as version_stack_recent_spec
        with (recent_spec_core).

  cpp.spec "monad::VersionStack<monad::AccountState>::recent() const"
      as version_stack_recent_const_spec
        with (recent_spec_core).

  #[global] Instance llll: LearnEq2 MapCurrentR := ltac:(solve_learnable).
(* Big-endian bytes of category/core/bytes.hpp's NULL_HASH (Keccak-256 of
   the empty byte string), in the integer representation used by bytes32R. *)
Definition null_code_hash : N :=
  89477152217924674838424037953991966239322087453347756267410168184682657981552%N.

Definition is_empty_model (oas: option AccountM) : bool :=
  match oas with
  | None => true
  | Some am => let ba := coreAc am in
      let ch := code_hash_of_program
                  (EVMOpSem.block.block_account_code ba) in
      let zn := w256_to_Z
                  (EVMOpSem.block.block_account_nonce ba) in
      let bn := w256_to_N
                  (EVMOpSem.block.block_account_balance ba) in
      (N.eqb ch null_code_hash)
      && (Z.eqb zn 0)
      && (N.eqb bn 0%N)
  end.

Definition is_dead_model (oas: option AccountM) : bool :=
  negb (bool_decide (is_Some oas)) || is_empty_model oas.
  
cpp.spec "monad::is_empty(const monad::Account&)" as is_empty_spec with (
  \arg{accountp: ptr} "account" (Vref accountp)
  \prepost{q ac} accountp |-> AccountR q ac
  \prepost{qnull} _global "monad::NULL_HASH" |-> bytes32R qnull null_code_hash
  \post[Vbool (is_empty_model (Some ac))] emp).

cpp.spec "monad::is_dead(const std::optional<monad::Account>&)" as is_dead_spec with (
  \arg{accountp: ptr} "account" (Vref accountp)
  \prepost{qnull} _global "monad::NULL_HASH" |-> bytes32R qnull null_code_hash
  \prepost{(oas: option AccountM)}
      accountp |-> optional_specs.optionR
                   "monad::Account"
                   AccountR 1 oas
  \post[Vbool (is_dead_model oas)] emp
).


(* TODO: generalize *)
cpp.spec "monad::VersionStack<monad::AccountState>::size() const"
  as versionstack_size_spec
  with (fun this:ptr =>
    \prepost{ls q}
        this |-> VersionStackR "monad::AccountState" UpdatedAccountStateR (cQp.mut q) ls
    \post[Vint (Z.of_nat (length ls))] emp
  ).

cpp.spec "monad::OriginalAccountState::min_balance() const"
  as accountstate_min_balance_spec
  with (fun this:ptr =>
    \prepost{orig_state} this |-> OriginalAccountStateR 1 orig_state
    \post[Vptr (this ,, _field "monad::OriginalAccountState::min_balance_")]
          emp).

cpp.spec "monad::OriginalAccountState::validate_exact_balance() const"
  as accountstate_validate_exact_balance_spec
  with (fun this:ptr =>
    \prepost{orig_state} this |-> OriginalAccountStateR 1 orig_state
    \post[Vbool (~~ bool_decide (is_Some (min_balance (assumExactness orig_state))))] emp).

(*
  NOTE ON get_code_hash, code maps, and collisions

  The C++ implementation stores code hashes inside accounts and stores the
  actual bytecode separately in hash-indexed caches/maps. Relevant excerpts:

  category/execution/ethereum/state3/account_state.hpp:
    [[nodiscard]] bytes32_t get_code_hash() const
    {
        if (MONAD_LIKELY(account_.has_value())) {
            return account_->code_hash;
        }
        return NULL_HASH;
    }

  category/execution/ethereum/state3/state.cpp:
    void State::set_code(Address const &address, byte_string_view const code)
    {
        auto const code_hash = to_bytes(keccak256(code));
        code_[code_hash] = vm().try_insert_varcode_raw(code_hash, code);
        account.value().code_hash = code_hash;
    }

    vm::SharedVarcode State::read_code(bytes32_t const &code_hash)
    {
        auto const it = code_.find(code_hash);
        if (it != code_.end()) { return it->second; }
        return block_state_.read_code(code_hash);
    }

  category/execution/ethereum/state2/block_state.cpp:
    vm::SharedVarcode BlockState::read_code(bytes32_t const &code_hash)
    {
        if (auto vcode = vm_.find_varcode(code_hash)) { return *vcode; }
        if (code_.find(it, code_hash)) {
            return vm_.try_insert_varcode(code_hash, it->second);
        }
        return vm_.try_insert_varcode(code_hash, db_.read_code(code_hash));
    }

  category/vm/varcode_cache.cpp:
    SharedVarcode VarcodeCache::try_set_raw(...)
    {
        if (!weight_cache_.find(acc, code_hash)) {
            return try_set(code_hash, make_shared_intercode(code));
        }
        return acc->second.value_;
    }

  Consequences:
  - State has a speculative cache: State::read_code consults State::code_ first,
    then BlockState (which itself consults the VM cache, then the block cache,
    then DB).
  - If two distinct bytecode blobs collide on the same hash, the first cached
    code "wins": try_set_raw returns the existing entry, so later code is
    ignored. Reads for that hash return the cached (old) code.
  - Optimistic execution compares only code_hash (see try_fix_account_mismatch),
    so a collision does not trigger a reexec. In a collision world, a tx may
    continue to observe old code even if a previous tx "updated" code to a
    different bytecode with the same hash.

  This spec therefore assumes collision resistance of code_hash, consistent
  with the EVM model where code_hash is a first-class field (EXTCODEHASH) and
  collisions are outside the model.
*)
cpp.spec "monad::AccountState::get_code_hash() const"
  from state_cpp.source as accountstate_get_code_hash_spec
  with (fun this:ptr =>
    \prepost{q (oas: option AccountM)}
        this |-> AccountStateRcore q oas
    \post{retp: ptr} [Vptr retp]
      retp |-> bytes32R 1
        (match oas with
         | None => 0%N
         | Some am =>
             code_hash_of_program
               (EVMOpSem.block.block_account_code (coreAc am))
         end)
  ).

cpp.spec "monad::operator==(const monad::Address&, const monad::Address&)" as address_eq_spec with(
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \prepost{(qa qb: Qp) (av bv: evm.address)}
      ap |-> addressR qa av
    ** bp |-> addressR qb bv
  \post[Vbool (bool_decide (av = bv))] emp
).

cpp.spec "monad::operator==(const monad::bytes32_t&, const monad::bytes32_t&)"
  from reserve_balance_cpp.source as reserve_balance_bytes32_eq_spec with (
    \arg{ap : ptr} "a" (Vref ap)
    \arg{bp : ptr} "b" (Vref bp)
    \prepost{qa av} ap |-> bytes32R qa av
    \prepost{qb bv} bp |-> bytes32R qb bv
    \post [Vbool (N.eqb av bv)] emp
  ).

#[global] Instance reserve_balance_bytes32_eq_spec_persistent :
  Persistent reserve_balance_bytes32_eq_spec.
Proof.
  unfold reserve_balance_bytes32_eq_spec.
  apply _.
Qed.

cpp.spec "monad::bytes32_t::bytes32_t(const monad::bytes32_t&)" as bytes32_copy_ctor_spec with (fun (this:ptr) =>
  \arg{otherp: ptr} "other" (Vref otherp)
  \prepost{(q: Qp) (v: Corelib.Numbers.BinNums.N)}
      otherp |-> bytes32R (cQp.mut q) v
  \post this |-> bytes32R (cQp.mut 1) v
).

cpp.spec "monad::bytes32_t::~bytes32_t()" as bytes32_dtor_spec with (fun (this:ptr) =>
  \pre{v} this |-> bytes32R (cQp.mut 1) v
  \post emp
).

cpp.spec "monad::bytes32_t::bytes32_t(const evmc_bytes32&)"
  from state_cpp.source as bytes32_evmc_bytes32_ctor_spec with (
    fun this : ptr =>
      \arg{initp : ptr} "" (Vref initp)
      \prepost initp |-> evmc_bytes32R 1
      \post this |-> bytes32R 1 0
  ).

cpp.spec "evmc_bytes32::~evmc_bytes32()"
  from state_cpp.source as evmc_bytes32_dtor_spec with (
    fun this : ptr =>
      \pre this |-> evmc_bytes32R 1
      \post emp
  ).

cpp.spec "monad::bytes32_t::operator=(const monad::bytes32_t&)"
  from state_cpp.source as bytes32_assign_spec with (
    fun this : ptr =>
      \arg{otherp : ptr} "" (Vref otherp)
      \pre{old : N} this |-> bytes32R 1 old
      \prepost{qother v} otherp |-> bytes32R qother v
      \post[Vref this] this |-> bytes32R 1 v
  ).

cpp.spec
  "monad_assertion_failed"
  from state_cpp.source as monad_assertion_failed_spec with (
    \arg{exprp : ptr} "" (Vptr exprp)
    \arg{funcp : ptr} "" (Vptr funcp)
    \arg{filep : ptr} "" (Vptr filep)
    \arg{line : Z} "" (Vint line)
    \arg{msgp : ptr} "" (Vptr msgp)
    \pre [| False |]
    \post emp
  ).

  #[global] Instance dec (i1 i2: Indices): Decision (i1=i2) := ltac:(solve_decision).



  (*
  cpp.spec "monad::vm::interpreter::Intercode::code() const"
    from reserve_balance_cpp.source as intercode_code_spec
    with (fun this:ptr =>
      \prepost{code} this |-> IntercodeR intercode_piece_qp code
      \post{retp: ptr} [Vptr retp] this |-> IntercodeR intercode_piece_qp code
    ).
 *)
  cpp.spec "monad::vm::interpreter::Intercode::size() const"
    from reserve_balance_cpp.source as intercode_size_spec
    with (fun this:ptr =>
      \prepost{code} this |-> IntercodeR intercode_piece_qp code
      \post{size: N} [Vn size]
        [| size = Z.to_N (evm.program_length  code) |]
    ).

  (*
  cpp.spec "monad::vm::Varcode::intercode() const"
    from reserve_balance_cpp.source as varcode_intercode_spec
    with (fun this:ptr =>
      \post{retp: ptr} [Vptr retp]
        Exists (ctrlid: CtrlBlockId) (code: evm.program) (owned: ptr),
          retp |-> @SharedPtrR _ _ _ _ (Tconst (Tnamed "monad::vm::interpreter::Intercode")) ctrlid
            (fun _ => IntercodeR intercode_piece_qp code) owned
    ).
   *)
  
  (* redundant: generic span_ctor_spec covers this constructor *)
(*
  cpp.spec "std::span<const unsigned char, 18446744073709551615ul>::span<const unsigned char*>(const unsigned char*, unsigned long)"
    from reserve_balance_cpp.source as span_const_uchar_ctor_spec
    with (fun this:ptr =>
      \arg{base: ptr} "ptr" (Vptr base)
      \arg{size: N} "count" (Vn size)
      \post this |-> SpanRbase "const unsigned char" 1 base size false
    ).
*)
(*
  cpp.spec "monad::vm::evm::is_delegated(std::span<const unsigned char, 18446744073709551615ul>)"
    from reserve_balance_cpp.source as is_delegated_spec
    with (
      \arg{spanp: ptr} "bytes" (Vptr spanp)
      \prepost{q base size sizeStaticallyKnown} spanp |-> SpanRbase "const unsigned char" q base size sizeStaticallyKnown
      \post{retb: bool} [Vbool retb] emp
    ).
 *)
  Definition sender_seen_in_current_prefix
      (ctx : MonadChainContext) (i : nat) (tx : TxWithHdr) : Prop :=
    exists j : nat,
      j <= i /\
      ((j < i /\
        nth_error (map sender (txsWithHdr (cblock ctx))) j = Some (sender tx)) \/
       exists auths,
         nth_error (map txAuthoritiesDelFrom (transactions (cblock ctx))) j = Some auths /\
         Some (sender tx) ∈ auths).

  (* The can_sender_dip_into_reserve contract is in reservebal_specs.v;
     cansenderdip.v proves the production body, including the prefix loop. *)
  (* Reserve-balance threshold computed by the dipped_into_reserve lambda. *)
  Definition reserve_violation_threshold_model
      (orig: MapModel evm.address AssumedPreTxAccountState)
      (*preBlockState: AugmentedState *)
      (addr sender: evm.address) (gas_fees: N) : option N :=
    let orig_bal := original_balance_pessimistic_model_map orig addr in
    let reserve := N.min DefReserve orig_bal in
    if asbool (addr = sender)
    then if N.ltb reserve gas_fees then None else Some (N.sub reserve gas_fees)
    else Some reserve.

  (* check_min_original_balance updates assumptions using the original balance. *)
  Definition check_min_original_balance_update
      (orig: MapModel evm.address AssumedPreTxAccountState)
      (addr: evm.address) (max_reserve: N)
      : MapModel evm.address AssumedPreTxAccountState :=
    let orig_bal := original_balance_pessimistic_model_map orig addr in
    update_assum_exactness_at addr
      (fun ex => min_balance_update ex orig_bal orig_bal max_reserve) orig.

	  Definition dipped_into_reserve_name : name :=
	    Ninst
	      (Nscoped (Nscoped (Nglobal (Nid "monad")) Nanonymous)
	         (Nfunction function_qualifiers.N "dipped_into_reserve"
		           [Tref (Qconst monad_address_ty);
		            Tref (Qconst (Tnamed "monad::Transaction"));
		            Tref (Qconst monad_uint256_ty);
		            Tulong;
		            Tref trace_state_tracer_ty;
		            Tref (Qconst (monad_chain_context_ty 10));
		            Tref (Tnamed "monad::State")]))
	      [Atype (monad_traits_ty 10)].

  Definition dipped_into_reserve_lam : name :=
    Nscoped dipped_into_reserve_name (Nanon 1).

  Definition dipped_into_reserve_capture_field (nm: ident) : field :=
    Nscoped dipped_into_reserve_lam (field_name.CaptureVar nm).

  Definition DippedIntoReserveLambdaR
      (addrp statep senderp gas_feesp: ptr) : Rep :=
	    (* Captured references are stored as fields in the lambda object. *)
	    (((o_field CU (dipped_into_reserve_capture_field "addr")
	          |-> refR<"monad::Address"> 1$m addrp)
	        ** o_field CU (dipped_into_reserve_capture_field "state")
	          |-> refR<"monad::State"> 1$m statep)
	      ** o_field CU (dipped_into_reserve_capture_field "sender")
	        |-> refR<"monad::Address"> 1$m senderp)
	    ** o_field CU (dipped_into_reserve_capture_field "gas_fees")
	      |-> refR<"monad::uint256_t"> 1$m gas_feesp
    ** structR dipped_into_reserve_lam 1$m.

  (* The old lambda records a lower bound; main records an exact balance.
     Suspend all its registrations: issues/reserve-balance-main-port.md.
  Definition dipped_into_reserve_lam_ctor_spec :=
    specify
      {| info_name := dipped_into_reserve_lam;
	         info_type :=
	           tFunction (Tnamed dipped_into_reserve_lam)
	             [Tref (Qconst monad_address_ty);
	              Tref (Tnamed "monad::State");
	              Tref (Qconst monad_address_ty);
	              Tref (Qconst monad_uint256_ty)] |} $
      \arg{addrp: ptr} "addr" (Vref addrp)
      \arg{statep: ptr} "state" (Vref statep)
      \arg{senderp: ptr} "sender" (Vref senderp)
      \arg{gas_feesp: ptr} "gas_fees" (Vref gas_feesp)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{qsender sender} senderp |-> addressR qsender sender
      \prepost{qfee gas_fees} gas_feesp |-> u256R qfee gas_fees
      \prepost{st} statep |-> StateR st
      \post{retp: ptr} [Vptr retp]
        retp |-> DippedIntoReserveLambdaR addrp statep senderp gas_feesp.

  Definition SpecFor_dipped_into_reserve_lam_ctor :=
    RegisterSpec dipped_into_reserve_lam_ctor_spec.
  #[global] Existing Instance SpecFor_dipped_into_reserve_lam_ctor.

  cpp.spec (dipped_into_reserve_lam .:: Nop function_qualifiers.Nc OOCall [])
    from reserve_balance_cpp.source as dipped_into_reserve_lam_call_spec
    with (fun this:ptr =>
      \prepost{addrp statep senderp gas_feesp}
        this |-> DippedIntoReserveLambdaR addrp statep senderp gas_feesp
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{qsender sender} senderp |-> addressR qsender sender
      \prepost{qfee gas_fees} gas_feesp |-> u256R qfee gas_fees
      \prepost statep |-> structR "monad::State" 1$m
      \pre{orig} statep |-> StateOriginalR orig
      \pre [| is_Some (mapModelLookup orig addr) |]
      \prepost{preBlockState qb bs (bsp: ptr)}
        statep ,, o_field CU "monad::State::block_state_"
          |-> refR<"monad::BlockState"> 1$m bsp
        ** bsp |-> BlockState.Rfrag preBlockState qb bs
      \post{retp: ptr} [Vptr retp]
        retp |-> optional_specs.optionR u256t u256R 1
                 (reserve_violation_threshold_model orig addr sender gas_fees)
        ** statep |-> StateOriginalR (check_min_original_balance_update orig addr DefReserve)
    ).

  cpp.spec (dipped_into_reserve_lam .:: Ndtor)
    from reserve_balance_cpp.source as dipped_into_reserve_lam_dtor_spec
    with (fun this:ptr =>
      \pre{addrp statep senderp gas_feesp}
        this |-> DippedIntoReserveLambdaR addrp statep senderp gas_feesp
      \post emp
    ).

  *)
cpp.spec "monad::Incarnation::Incarnation(const monad::Incarnation&)"
  as incarnation_copy_spec with (fun this:ptr =>
  \arg{otherp:ptr} "other" (Vref otherp)
  \prepost{(q:cQp.t) (idx: Indices)}
      otherp |-> IncarnationR q idx
  \post
      this |-> IncarnationR (cQp.mut 1) idx).

cpp.spec "monad::Incarnation::~Incarnation()"
  from state_cpp.source as incarnation_dtor_spec with (
    fun this : ptr =>
      \pre{inc} this |-> IncarnationR 1 inc
      \post emp
  ).

(* 4. Incarnation equality: monad::operator==(monad::Incarnation, monad::Incarnation) *)
cpp.spec "monad::operator==(monad::Incarnation, monad::Incarnation)" as incarnation_eq_spec with (
  \arg{i1p: ptr} "i1" (Vref i1p)
  \arg{i2p: ptr} "i2" (Vref i2p)
  \prepost{(q1 q2: Qp) (idx1 idx2: Indices)}
      i1p |-> IncarnationR (cQp.mut q1) idx1
    ** i2p |-> IncarnationR (cQp.mut q2) idx2
  \post[Vbool (bool_decide (idx1 = idx2))] emp
      ).

#[global] Instance : LearnEq2 u256R := ltac:(solve_learnable).

  Lemma observeOrigState (state_addr:ptr) q t:
    Observe (type_ptr "monad::OriginalAccountState" state_addr)
            (state_addr |-> OriginalAccountStateR q t).
  Proof using. Admitted.

  Lemma observeState (state_addr:ptr) q t:
    Observe (type_ptr "monad::AccountState" state_addr)
            (state_addr |-> UpdatedAccountStateR q t).
  Proof using. Admitted.
  
  Lemma observeBytes32 (bp:ptr) q v:
    Observe (type_ptr "monad::bytes32_t" bp)
            (bp |-> bytes32R q v).
  Proof using.
    unfold bytes32R.
    apply _.
  Qed.

  Definition observeStateF r q t:= @observe_fwd _ _ _ (observeState r q t).
  Definition observeOrigStateF r q t:= @observe_fwd _ _ _ (observeOrigState r q t).
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

  Lemma observeBlockStateRfragTypePtr
      (bp : ptr) preBlockState q g :
    Observe (type_ptr "monad::BlockState" bp)
            (bp |-> BlockState.Rfrag preBlockState q g).
  Proof using. Admitted.

  Definition observeBlockStateRfragTypePtrF bp preBlockState q g :=
    @observe_fwd _ _ _ (observeBlockStateRfragTypePtr bp preBlockState q g).

  Lemma observeVersionStackSpineTypePtr
      (cppType : type) (q : Qp) (lt : list ptr) :
    Observe (type_ptrR (VersionStack_ty cppType))
            (VersionStackSpineR cppType q lt).
  Proof using. Admitted.

  Definition observeVersionStackSpineTypePtrF
      (cppType : type) (q : Qp) (lt : list ptr) :=
    ltac:(mk_at_obs_fwd
      (observeVersionStackSpineTypePtr cppType q lt)).

  Lemma version_stack_spine_keep_type_ptr
      (p : ptr) (cppType : type) (q : Qp) (lt : list ptr) :
    p |-> VersionStackSpineR cppType q lt
    |--
    p |-> VersionStackSpineR cppType q lt
    ** type_ptr (VersionStack_ty cppType) p.
  Proof using.
    rewrite <- _at_type_ptrR.
    rewrite <- _at_sep.
    apply _at_mono.
    apply (@observe_elim _ _
      (VersionStackSpineR cppType q lt)
      (observeVersionStackSpineTypePtr cppType q lt)).
  Qed.

  Definition version_stack_spine_keep_type_ptr_C
      (p : ptr) (cppType : type) (q : Qp) (lt : list ptr) :=
    [CANCEL] (version_stack_spine_keep_type_ptr p cppType q lt).

  Set Printing Coercions.

  Lemma observeState2 (state_addr:ptr) t: 
    Observe (type_ptr (Tnamed "monad::State") state_addr)
            (state_addr |-> StateR t).
  Proof using. Admitted.
  Definition observeStateF2 r t := @observe_fwd _ _ _ (observeState2 r t).
(*            ** (reference_to "monad::State" this)). (* convenient but logically redundant *) *)

#[global] Instance : LearnEq2 (addressR) := ltac:(solve_learnable).
#[global] Instance : LearnEq2 optionAddressR := ltac:(solve_learnable).
#[global] Instance : LearnEq1 (StateR) := ltac:(solve_learnable).
#[global] Instance : LearnEq2 bytes32R := ltac:(solve_learnable).

Definition update_assum_exactness_map
           (m: MapModel evm.address AssumedPreTxAccountState)
           (updates: gmap evm.address AssumptionExactness)
  : MapModel evm.address AssumedPreTxAccountState :=
  map (fun p =>
         let '(addr, (loc, aps)) := p in
         match updates !! addr with
         | Some ex =>
             (addr, (loc, {| preTxState := preTxState aps;
                             preTxStorage := preTxStorage aps;
                             assumExactness := ex |}))
         | None => p
         end) m.

(* TODO(temporary): copied from execproofs/reservebal/reserve_balance.v; delete there later.
   - update_assum_exactness_state
   - min_balance_stricter
   - assumption_exactness_stricter
   - updates_stricter
   - gdom, gdomemp
   - updates_stricter_emp
*)
Definition update_assum_exactness_state
           (st: StateM)
           (updates: gmap evm.address AssumptionExactness) : StateM :=
  {| relaxedValidation := relaxedValidation st;
     preTxAssumedState := update_assum_exactness_map (preTxAssumedState st) updates;
     newStates := newStates st;
     blockStatePtr := blockStatePtr st;
     indices := indices st;
     blockStateGloc := blockStateGloc st;
     dbBlockStateCodeMapLb := dbBlockStateCodeMapLb st;
     codeMap := codeMap st;
  |}.

Definition min_balance_stricter (old new: option N) : Prop :=
  match old, new with
  | None, None => True
  | None, Some _ => False
  | Some _, None => True
  | Some m, Some m' => (m <= m')%N
  end.

Definition assumption_exactness_stricter
           (old new: AssumptionExactness) : Prop :=
  min_balance_stricter (min_balance old) (min_balance new)
  /\ (nonce_exact old = true -> nonce_exact new = true).

Definition updates_stricter
           (st: StateM)
           (updates: gmap evm.address AssumptionExactness) : Prop :=
  forall addr ex,
    updates !! addr = Some ex ->
    exists loc aps,
      preTxAssumedState st !! addr = Some (loc, aps)
      /\ assumption_exactness_stricter (assumExactness aps) ex.

Definition gdom {K V} `{Countable K} (g: gmap K V) : list K :=
  map fst (map_to_list g).

Lemma gdomemp {K V} `{Countable K} : @gdom K V _ _ ∅ = [].
Proof using. reflexivity. Qed.

Lemma updates_stricter_emp stm : updates_stricter stm ∅.
Proof using.
  unfold updates_stricter.
  intros.
  rewrite lookup_empty in H.
  discriminate.
Qed.

End with_Sigma.

Section reserve_balance_helpers.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

  Lemma empupd (m : MapModel evm.address AssumedPreTxAccountState) :
    update_assum_exactness_map m ∅ = m.
  Proof.
    unfold update_assum_exactness_map.
    autorewrite with syntactic.
    rewrite -> map_ext with (g := fun x => x); [apply map_id|].
    intros.
    destruct a as [addr [loc aps]].
    rewrite lookup_empty.
    reflexivity.
  Qed.

  Lemma mpmp {K V} (foo : MapModel K V) :
    map (fun x => (let '(a, (b, _)) := x in (a, b)).2) foo = map (fun x => x.2.1) foo.
  Proof.
    apply map_ext.
    intros.
    destruct a as [k [p v]]; reflexivity.
  Qed.

  Lemma mpmp1 {K V} (foo : MapModel K V) :
    map (fun x => (let '(a, (b, _)) := x in (a, b)).1) foo = map fst foo.
  Proof.
    apply map_ext.
    intros.
    destruct a as [k [p v]]; reflexivity.
  Qed.

  Lemma updsame (stm : StateM) (t : gmap evm.address AssumptionExactness) :
    map fst (update_assum_exactness_map (preTxAssumedState stm) t) = map fst (preTxAssumedState stm).
  Proof.
    induction (preTxAssumedState stm) as [| [addr [loc aps]] tl IH]; simpl; auto.
    case_match; simpl; rewrite IH; reflexivity.
  Qed.
End reserve_balance_helpers.

Definition isAccountDelegated (o : option AccountM) : bool :=
  match o with
  | Some am => isDelegationMarker (block.block_account_code (coreAc am))
  | None => false
  end.

#[global] Hint Resolve observeStateF2 : sl_opacity.
#[global] Hint Resolve updates_stricter_emp : pure.
#[global] Hint Rewrite @lookup_empty @map_id : syntactic.
#[global] Hint Rewrite @gdomemp empupd : syntactic.
#[global] Hint Rewrite @map_map @mpmp @nth_error_map : syntactic.


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
#[global] Opaque BlockHashBufferR.
#[global] Hint Opaque BlockHashBufferR: sl_opacity.
#[global] Opaque BheaderR.
#[global] Hint Opaque BheaderR : sl_opacity.
#[global] Opaque TransactionR.
#[global] Hint Opaque TransactionR : sl_opacity.
#[global] Opaque StateR.
#[global] Hint Opaque StateR : sl_opacity.
#[only(lens)] derive StateM.
#[global]  Hint Resolve observeStateF observeOrigStateF observeBytes32F
  observeBytes32RangeF observeU256F observeU256RangeF
  observeBlockStateRfragTypePtrF observeVersionStackSpineTypePtrF
  version_stack_spine_keep_type_ptr_C: sl_opacity.
Definition dummyTx : TxWithHdr. Proof. Admitted.

Definition base_fee_per_gas (b: Block) : w256 :=
  match (base_fee_per_gas (header b)) with
  | Some s => s
  | None => 0%N
  end.

Lemma lengthZ_txsWithHdr (b : Block) :
  lengthZ (txsWithHdr b) = lengthZ (transactions b).
Proof.
  unfold txsWithHdr.
  autorewrite with syntactic.
  reflexivity.
Qed.
#[global] Hint Rewrite lengthZ_txsWithHdr : syntactic.

Lemma sender_map_transactions_txsWithHdr (b : Block) :
  map (fun t : Transaction => sender (t, header b)) (transactions b) =
  map sender (txsWithHdr b).
Proof.
  unfold txsWithHdr.
  rewrite map_map.
  reflexivity.
Qed.
#[global] Hint Rewrite sender_map_transactions_txsWithHdr : syntactic.

Hint Opaque TransactionR : typeclass_instances.
#[only(lazy_unfold)] derive TransactionR.
#[only(lazy_unfold)] derive AccountR.
#[only(lazy_unfold)] derive StateR.
#[only(eager_unfold)] derive DippedIntoReserveLambdaR.
#[only(eager_unfold)] derive UpdatedAccountStateR.
#[only(eager_unfold)] derive pairR.
#[only(eager_unfold)] derive VersionStackR.
#[only(eager_unfold)] derive StateOriginalR.
#[only(eager_unfold)] derive AnkerMapSliceR.
#[only(eager_unfold)] derive MonadChainContextR.

Section reserve_balance_proof_env.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

#[global] Instance kjsfdjs {T} a : LearnEq3 (@VersionStackR _ _ _ T a) := ltac:(solve_learnable).
#[global] Instance kjfslksfdjs a : LearnEq2 (@VersionStackSpineR _ _ _ a) := ltac:(solve_learnable).
#[global] Instance learnStateDirtyStackR : LearnEq2 StateDirtyStackR := ltac:(solve_learnable).

#[global] Instance ll : LearnEq2 AccountStateRcore := ltac:(solve_learnable).
#[global] Instance lll : LearnEq2 MonadChainContextR := ltac:(solve_learnable).

End reserve_balance_proof_env.

#[global] Hint Unfold ModelWithPtr : unfold.

#[global] Hint Opaque OriginalAccountStateR : sl_opacity.
#[global] Hint Opaque SharedPtrR : sl_opacity.
#[global] Hint Opaque AccountStateRcore : sl_opacity.
#[global] Hint Opaque StorageMapR : sl_opacity.
#[global] Hint Opaque VersionStackR : sl_opacity.
#[global] Hint Opaque StateDirtyStackR : sl_opacity.
#[global] Hint Opaque optionAddressR : sl_opacity.
#[global] Hint Opaque VectorR : sl_opacity.
#[global] Hint Opaque atomicR : sl_opacity.
#[global] Hint Opaque MonadChainContextR : sl_opacity.
#[global] Hint Opaque blockStatePtr : sl_opacity.
#[global] Hint Opaque specify.exact.method : sl_opacity.
#[global] Hint Opaque gas_price_traits_spec : sl_opacity.
#[global] Hint Opaque authsp : sl_opacity.
#[global] Hint Opaque sendersp : sl_opacity.
#[global] Hint Opaque std.vector.base_pointer : sl_opacity.
#[global] Hint Opaque LogsR : sl_opacity.
#[global] Hint Opaque DippedIntoReserveLambdaR StateOriginalR : sl_opacity.
#[global] Hint Opaque pairR : sl_opacity.
#[global] Hint Opaque AnkerMapSliceR : sl_opacity.
#[global] Hint Opaque incarnation_copy_spec : sl_opacity.
#[global] Hint Opaque incarnation_dtor_spec : sl_opacity.
#[global] Hint Opaque account_state_set_storage_spec : sl_opacity.
#[global] Hint Opaque state_set_storage_spec : sl_opacity.
#[global] Hint Opaque account_dtor_spec : sl_opacity.
#[global] Hint Opaque account_substate_touch_spec : sl_opacity.
#[global] Hint Opaque uint256_max_spec : sl_opacity.
#[global] Hint Opaque state_current_account_state_update_spec : sl_opacity.
(* #[global] Hint Opaque state_check_min_balance_borrowed_spec : sl_opacity. *)
#[global] Hint Opaque optional_account_has_value_spec : sl_opacity.
#[global] Hint Opaque optional_account_value_spec : sl_opacity.
#[global] Hint Opaque optional_account_bool_spec : sl_opacity.
#[global] Hint Opaque optional_account_arrow_spec : sl_opacity.
#[global] Hint Opaque optional_account_arrow_const_spec : sl_opacity.
#[global] Hint Opaque monad_assertion_failed_spec : sl_opacity.
#[global] Hint Opaque bytes32_evmc_bytes32_ctor_spec : sl_opacity.
#[global] Hint Opaque evmc_bytes32_dtor_spec : sl_opacity.
#[global] Hint Opaque bytes32_assign_spec : sl_opacity.
#[global] Hint Opaque reserve_balance_bytes32_eq_spec : sl_opacity.
#[global] Hint Opaque StateCodeMapR : sl_opacity.

#[global] Opaque AccountStateRcore.
#[global] Opaque AccountSubstateR.
#[global] Opaque StateDirtyStackR.

Section reserve_balance_proof_env2.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.

#[global] Instance fsksdjfk q1 q2 :
  Refine1 false false (u256R q1 = u256R q2) [q1 = q2] :=
  ltac:(constructor; auto).

#[global] Instance codeMapInv (p : ptr) st :
  Observe [| stateCodeMapInvariants st |] (p |-> StateCodeMapR st) := _.
Definition observeCodeInv r t := @observe_fwd _ _ _ (codeMapInv r t).
Hint Resolve observeCodeInv : sl_opacity.
#[global] Instance LearnEq1_StateCodeMapR : LearnEq1 StateCodeMapR :=
  ltac:(solve_learnable).

Lemma borrowIndex_at (q : Qp) {K V : Type} {eqd : EqDecision K}
  (tykey tyval : type) (krep : Qp -> K -> Rep) (vrep : Qp -> V -> Rep)
  (m : MapModel K V) (borrowIndex : N) bt btk (p : ptr) :
  nth_error m (N.to_nat borrowIndex) = Some bt ->
  btk = bt.1 ->
  p |-> AnkerMapPayloadsR tykey tyval krep vrep q m -|-
    ((bt.2.1 |-> pairR tykey tyval krep vrep (q / 2) q (bt.1, bt.2.2)))
      ** p |-> AnkerMapPayloadsR tykey tyval krep vrep q (removeKey m btk).
Proof. Admitted.

End reserve_balance_proof_env2.

Arguments txsWithHdr /.

Ltac unborrowAnkerPayload :=
  unshelve (wapplyRev borrowIndex_at);
  try eagerUnifyC;
  try match goal with
      | H : nth_error ?l _ = _ |- nth_error ?l _ = _ => exact H
      end;
  eauto.

Ltac case_bool_decide_inner :=
  repeat rewrite bool_decide_decide;
  case_decide_inner;
  repeat rewrite <- bool_decide_decide;
  repeat match goal with
         | H : _ = left _ |- _ => clear H
         end.

Ltac unifyPayload :=
  permLR ltac:(fun L _ R _ =>
    match L with
    | _ |-> AnkerMapPayloadsR _ _ _ _ _ _ =>
        match R with
        | _ |-> AnkerMapPayloadsR _ _ _ _ _ _ => unify L R
        end
    end).

#[global] Hint Resolve observeCodeInv : sl_opacity.

Section reserve_balance_specs.
  Context `{Sigma : cpp_logic} {CU : genv} {hh : HasOwn mpredI fracR}.
  Context {MODd : reserve_balance_cpp.source ⊧ CU}.

  Definition SpecFor_address_set_contains :=
    ankerl_specs.SpecFor_anker_set_contains.
  #[global] Existing Instance SpecFor_address_set_contains.

  Definition SpecFor_ranges_contains_optional_address :=
    RegisterSpec
      (ranges_specs.ranges_contains_optional_address_spec
         (fun q xs => std.vector.R "std::optional<monad::Address>" q xs)
         addressR).
  #[global] Existing Instance SpecFor_ranges_contains_optional_address.

  cpp.spec
    ("monad::get_max_reserve(const monad::Address&)"
       .<< Atype (monad_traits_ty 10) >>)
    from reserve_balance_cpp.source as get_max_reserve_spec with (
      \arg{addrp: ptr} "address" (Vref addrp)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \post{retp: ptr} [Vptr retp] retp |-> u256R 1 DefReserve
    ).

  cpp.spec "monad::OriginalAccountState::set_validate_exact_balance()"
    from state_cpp.source as accountstate_set_validate_exact_balance_spec with (fun origp : ptr =>
      \pre{orig_state} origp |-> OriginalAccountStateR 1 orig_state
      \post origp |-> OriginalAccountStateR 1
        (update_assum_exactness_assumed exact_balance_update orig_state)
    ).

  cpp.spec "monad::OriginalAccountState::set_min_balance(const monad::uint256_t&)"
    from state_cpp.source as accountstate_set_min_balance_spec with (fun origp : ptr =>
      \arg{valuep : ptr} "value" (Vref valuep)
      \prepost{(qv : Qp) value} valuep |-> u256R qv$c value
      \pre{orig_state}
        origp |-> OriginalAccountStateR 1 orig_state
      \pre [| is_Some (preTxState orig_state) |]
      \pre [| (value <= original_balance_pessimistic_model_assumed orig_state)%N |]
      \post origp |-> OriginalAccountStateR 1
        (set_min_balance_update_assumed orig_state value)
    ).

  cpp.spec "monad::State::original_account_state(const monad::Address&)"
    from state_cpp.source as state_original_account_state_spec with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost this |-> structR "monad::State" 1$m
      \pre{orig}
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                addressR OriginalAccountStateR 1 orig
      \pre
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                addressToN addressR 1
                (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
      \prepost{(block_statep : ptr) (preBlockState : AugmentedState)
                (g : BlockState.glocs) (qblock : Qp)}
        this ,, o_field CU "monad::State::block_state_"
          |-> refR<"monad::BlockState"> 1$m block_statep
        ** block_statep |-> BlockState.Rfrag preBlockState qblock g
      \post{origp : ptr} [Vref origp]
        Exists (loc : ptr),
        Exists (orig_final : MapModel evm.address AssumedPreTxAccountState),
        Exists (orig_state : AssumedPreTxAccountState),
          this ,, o_field CU "monad::State::original_"
            |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                  addressR OriginalAccountStateR 1 orig_final
          ** this ,, o_field CU "monad::State::original_"
            |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                  addressToN addressR 1
                  (map (fun '(a1, (b0, _)) => (a1, b0)) orig_final)
          ** [| state_original_account_state_post
                 orig addr orig_final loc orig_state |]
          ** [| origp = loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState" |]
    ).

  (* Obsolete helpers and the suspended top-level reserve contract.
     See issues/reserve-balance-main-port.md. No registrations survive here.
  cpp.spec "monad::State::check_account_min_balance(monad::OriginalAccountState&, const std::optional<monad::Account>&, const monad::uint256_t&)"
    from state_cpp.source as state_check_account_min_balance_spec with (fun this : ptr =>
      \arg{origp : ptr} "original_state" (Vref origp)
      \arg{accountp : ptr} "account" (Vref accountp)
      \arg{valuep : ptr} "debit" (Vref valuep)
      \prepost{(qv : Qp) value} valuep |-> u256R qv$c value
      \pre{orig addr loc orig_state}
        [| mapModelLookup orig addr = Some (loc, orig_state) |]
      \pre [| origp = loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState" |]
      \pre
        loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
             |-> addressR (1 / 2) addr
      \pre
        origp |-> OriginalAccountStateR 1 orig_state
      \pre
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                addressR OriginalAccountStateR 1 (removeKey orig addr)
      \prepost
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                addressToN addressR 1
                (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
      \pre [| accountp =
                 origp
                   ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
                   ,, o_field CU "monad::AccountState::account_" |]
      \post{retb : bool} [Vbool retb]
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                addressR OriginalAccountStateR 1
                (check_min_original_balance_update orig addr value)
        ** [| retb = check_min_balance_ok
                     (original_balance_pessimistic_model_map orig addr)
                     value |]
    ).

  cpp.spec "monad::State::check_min_original_balance(const monad::Address&, const monad::uint256_t&)"
    from state_cpp.source as state_check_min_original_balance_spec with (fun this:ptr =>
      \arg{addrp: ptr} "address" (Vref addrp)
      \arg{valuep: ptr} "value" (Vref valuep)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{(qv : Qp) value} valuep |-> u256R qv$c value
      \prepost this |-> structR "monad::State" 1$m
      \pre{orig}
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                addressR OriginalAccountStateR 1 orig
      \prepost
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                addressToN addressR 1
                (map (λ '(a1, (b0, _)), (a1, b0)) orig)
      \prepost{(block_statep : ptr) (preBlockState : AugmentedState)
                (g : BlockState.glocs) (qblock : Qp)}
        this ,, o_field CU "monad::State::block_state_"
          |-> refR<"monad::BlockState"> 1$m block_statep
        ** block_statep |-> BlockState.Rfrag preBlockState qblock g
      \pre [| is_Some (mapModelLookup orig addr) |]
      \post{retb: bool} [Vbool retb]
        let orig_bal := original_balance_pessimistic_model_map orig addr in
        let ok := check_min_balance_ok orig_bal value in
        this ,, o_field CU "monad::State::original_"
             |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                   addressR OriginalAccountStateR 1
                   (check_min_original_balance_update orig addr value)
        ** [| retb = ok |]
    ).

  (* begin show *)
  cpp.spec (functionNamed reserve_balance_cpp.source "dipped_into_reserve") as dipped_into_reserve_spec with (
  \arg{senderp: ptr} "sender" (Vref senderp)
  \let{(ctx: MonadChainContext) (i: nat)} tx := nth i (txsWithHdr (cblock ctx)) dummyTx
  \pre [| (Z.of_nat i < lengthZ (transactions (currentBlock (blocks ctx))))%Z |]
  \pre [| validTx tx |]
  \prepost{qsender } senderp |-> addressR qsender (sender tx)
  \arg{txp: ptr} "tx" (Vref txp)
  \prepost{qtx } txp |-> TransactionR qtx tx.1
  \arg{basefeep: ptr} "base_fee_per_gas" (Vref basefeep)
  \prepost{qfee} basefeep |-> u256R qfee (base_fee_per_gas (cblock ctx))
  \arg "i" (Vint i)
  \arg{state_tracerp: ptr} "state_tracer" (Vref state_tracerp)
  \arg{ctxp: ptr} "ctx" (Vref ctxp)
  \prepost{qctx} ctxp |-> MonadChainContextR qctx ctx
  \pre{hist: ExtraAcStates} [| historyConsistent ctx hist  /\ forall addr, configuredReserveBal (hist addr) = DefReserve |]%N
  \arg{statep: ptr} "state" (Vref statep)
  \pre{(qstate:Qp) (st: StateM)} statep |-> StateR st
  \pre [| forall (i0 : N)
                 (nthElemPtr0 nthElemVstackTopPtr0 : ptr)
                 (nthElemVstackTop0 : UpdatedAccountState)
                 (nthElemVstackTl0 : list (ptr * UpdatedAccountState)),
            nth_error (newStates st) (N.to_nat i0) =
              Some (sender tx, (nthElemPtr0, (nthElemVstackTopPtr0, nthElemVstackTop0) :: nthElemVstackTl0)) ->
            match
              mapModelLookup
                (check_min_original_balance_update
                   (preTxAssumedState st) (sender tx) DefReserve)
                (sender tx)
            with
            | Some (_, aps) =>
                match postTxState nthElemVstackTop0 with
                | Some am => isDelegationMarker (block.block_account_code (coreAc am))
                | None => false
                end =
                match preTxState aps with
                | Some am => isDelegationMarker (block.block_account_code (coreAc am))
                | None => false
                end && asbool (sender tx ∉ undels tx.1.2) || asbool (sender tx ∈ dels tx.1.2)
            | None => False
            end |]
  \prepost{preBlockState bs qb} blockStatePtr st |-> BlockState.Rfrag preBlockState qb bs
  \prepost{qnull} _global "monad::NULL_HASH" |-> bytes32R qnull 0
  \post{retb:bool} [Vbool retb]
    Exists (updates: gmap evm.address AssumptionExactness),
      let stf := update_assum_exactness_state st updates in
      statep |-> StateR stf **
      [| updates_stricter st updates |] **
      [| forall (preTxState: StateOfAccounts),
          satisfiesAssumptions stf preTxState ->
          let postTxState :=  (applyUpdates stf preTxState) in
          let changedAcs := (map fst (newStates st)) in
          retb = negb (allFinalBalSufficient 3 (preTxState, hist) postTxState changedAcs tx)
      |]).
  (* end show *)
  *)

End reserve_balance_specs.

(* ------------------------------------------------------------------------- *)
(* VersionStack and dirty_ summary (C++ State::version_ / State::dirty_)       *)
(* ------------------------------------------------------------------------- *)
(* In the C++ implementation, State::version_ indexes a stack of per-callframe
   checkpoints. Each State::push() increments version_ and starts a new layer,
   and each pop_accept/pop_reject decrements it. These layers correspond to
   nested call/create frames (and other rollback points), not to speculative
   parallel execution.

   VersionStack stores (version, value) pairs only for versions where an account
   is *touched* (i.e., current(version) is requested). Therefore the stored
   version numbers are monotone but can be non-contiguous: if an account is not
   modified in some intermediate call frame, no entry is pushed for that frame.

   The deque State::dirty_ tracks, per version, the set of addresses touched
   in that layer. On pop_reject, we iterate only those addresses to roll back
   their VersionStacks and erase accounts whose stacks become empty.

   StateR currently models only the top-level execution state: version_ is 0
   and dirty_ is empty.  Full nested VersionStack/dirty_ behavior is still
   TODO. *)

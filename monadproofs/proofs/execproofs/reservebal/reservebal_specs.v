Require Import monad.proofs.exec_specs.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.reservebalold.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.libspecs.ankerl_specs.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.u256_specs.
Require Import skylabs.auto.cpp.proof.

Import exec_specs.

Set Default Goal Selector "!".
Open Scope N_scope.

Section with_Sigma.
  Context `{Sigma : cpp_logic} {CU : genv}.
  Context {MODd : state_cpp.source ⊧ CU}.

  cpp.spec "monad::State::current_account(const monad::Address&)"
    from state_cpp.source as state_current_account_option_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \pre{st} this |-> StateR st
      \pre{F : option AccountM -> option AccountM} emp
      \prepost{preBlockState bs qb}
        blockStatePtr st |-> BlockState.Rfrag preBlockState qb bs
      \post{retp : ptr} [Vref retp]
        Exists st_final,
        Exists statep,
        Exists upd,
          retp |-> optional_specs.optionR
            "monad::Account"%cpp_type AccountR 1
            (postTxState upd)
          ** (retp |-> optional_specs.optionR
                "monad::Account"%cpp_type AccountR 1
                (F (postTxState upd)) -*
              this |-> StateR
                (state_update_current_account st_final addr
                   {| postTxState := F (postTxState upd);
                      substateModel := substateModel upd |}))
          ** [| retp =
                 statep ,, o_field CU "monad::AccountState::account_" |]
          ** [| state_current_account_state_post
                 st addr st_final statep upd |]
    ).

  Definition state_recent_account_slice_post
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (cur : MapModel evmopsem.evm.address (list (ptr * UpdatedAccountState)))
      (addr : evmopsem.evm.address)
      (orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (loc accountp : ptr)
      (orig_state : AssumedPreTxAccountState)
      (acct : option AccountM) : Prop :=
    match mapModelLookup cur addr with
    | Some (_, updates) =>
        exists upd_loc upd tl,
          updates = (upd_loc, upd) :: tl
          /\ orig_final = orig
          /\ accountp =
               upd_loc ,, o_field CU "monad::AccountState::account_"
          /\ acct = postTxState upd
    | None =>
        state_original_account_state_post orig addr orig_final loc orig_state
        /\ accountp =
             loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState"
                 ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
                 ,, o_field CU "monad::AccountState::account_"
        /\ acct = preTxState orig_state
    end.

  cpp.spec "monad::State::recent_account(const monad::Address&)"
    from state_cpp.source as state_recent_account_slice_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \pre{orig}
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                addressR OriginalAccountStateR 1 orig
      \pre
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                addressToN addressR 1
                (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
      \prepost{preBlockState bs qb (bsp : ptr)}
        this ,, o_field CU "monad::State::block_state_"
          |-> refR<"monad::BlockState"> 1$m bsp
        ** bsp |-> BlockState.Rfrag preBlockState qb bs
      \prepost{qcur cur}
        StateCurrentLookupR this qcur addr cur
      \prepost this |-> structR "monad::State" 1$m
      \post{accountp : ptr} [Vref accountp]
        Exists (orig_final : MapModel evmopsem.evm.address AssumedPreTxAccountState),
        Exists (loc : ptr),
        Exists (orig_state : AssumedPreTxAccountState),
        Exists (acct : option AccountM),
          this ,, o_field CU "monad::State::original_"
            |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                  addressR OriginalAccountStateR 1 orig_final
          ** this ,, o_field CU "monad::State::original_"
            |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                  addressToN addressR 1
                  (map (fun '(a1, (b0, _)) => (a1, b0)) orig_final)
          ** reference_to "std::optional<monad::Account>" accountp
          ** [| state_recent_account_slice_post
                 orig cur addr orig_final loc accountp orig_state acct |]
    ).

  Definition check_min_balance_update_with_account
      (orig : MapModel evmopsem.evm.address AssumedPreTxAccountState)
      (addr : evmopsem.evm.address)
      (acct : option AccountM)
      (value : N) :
      MapModel evmopsem.evm.address AssumedPreTxAccountState :=
    update_assum_exactness_at addr
      (fun ex =>
         min_balance_update ex
           (original_balance_pessimistic_model_map orig addr)
           (balanceOfAccount acct)
           value)
      orig.

  Definition check_account_min_balance_accountR
      (current_account : option (ptr * UpdatedAccountState))
      (origp accountp : ptr)
      (orig_state : AssumedPreTxAccountState)
      (acct : option AccountM) : mpred :=
    match current_account with
    | Some (current_accountp, upd) =>
        [| accountp =
             current_accountp
               ,, o_field CU "monad::AccountState::account_" |]
        ** [| acct = postTxState upd |]
        ** current_accountp |-> UpdatedAccountStateR 1 upd
    | None =>
      [| accountp =
           origp
             ,, o_base CU "monad::OriginalAccountState" "monad::AccountState"
             ,, o_field CU "monad::AccountState::account_" |]
      ** [| acct = preTxState orig_state |]
    end.

  (* Removed C++ helper; see issues/reserve-balance-main-port.md.
  cpp.spec "monad::State::check_account_min_balance(monad::OriginalAccountState&, const std::optional<monad::Account>&, const monad::uint256_t&)"
    from state_cpp.source as state_check_account_min_balance_recent_spec
    with (fun this : ptr =>
      \arg{origp : ptr} "original_state" (Vref origp)
      \arg{accountp : ptr} "account" (Vref accountp)
      \arg{valuep : ptr} "debit" (Vref valuep)
      \prepost{qv value} valuep |-> u256R qv value
      \pre{orig addr loc orig_state acct current_account}
        [| mapModelLookup orig addr = Some (loc, orig_state) |]
      \pre [| origp = loc ,, pairSndOffset "monad::Address" "monad::OriginalAccountState" |]
      \pre
        loc |-> pairFstOffset "monad::Address" "monad::OriginalAccountState"
             |-> addressR (1 / 2) addr
      \pre
        origp |-> OriginalAccountStateR 1 orig_state
      \prepost
        check_account_min_balance_accountR
          current_account origp accountp orig_state acct
      \pre
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                addressR OriginalAccountStateR 1 (removeKey orig addr)
      \prepost
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                addressToN addressR 1
                (map (fun '(a1, (b0, _)) => (a1, b0)) orig)
      \post{retb : bool} [Vbool retb]
        this ,, o_field CU "monad::State::original_"
          |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                addressR OriginalAccountStateR 1
                (check_min_balance_update_with_account orig addr acct value)
        ** [| retb = check_min_balance_ok (balanceOfAccount acct) value |]
    ).

  *)
  Definition version_stack_account_state_current_spec : mpred :=
    let cls :=
      ("monad::VersionStack".<<
         Atype "monad::AccountState"
       >>)%cpp_name in
    let args := [Tuint] in
    templated_method
      (Nscoped cls (Nfunction function_qualifiers.N "current" args))
      cls function_qualifiers.N (Tref "monad::AccountState") args $
      \this this
      \arg "version" (Vint 0)
      \pre{h upd tl}
        this |-> VersionStackSpineR "monad::AccountState" 1
          (h :: map fst tl)
        ** ([∗ list] p ∈ tl,
              let '(loc, val0) := p in
              (loc : ptr) |-> UpdatedAccountStateR 1 val0)
        ** h |-> UpdatedAccountStateR 1 upd
      \post[Vref h]
        this |-> VersionStackSpineR "monad::AccountState" 1
          (h :: map fst tl)
        ** ([∗ list] p ∈ tl,
              let '(loc, val0) := p in
              (loc : ptr) |-> UpdatedAccountStateR 1 val0)
        ** h |-> UpdatedAccountStateR 1 upd.
End with_Sigma.

Definition SpecFor_version_stack_account_state_current :=
  RegisterSpec (@version_stack_account_state_current_spec).
#[global] Existing Instance SpecFor_version_stack_account_state_current.

#[global] Hint Opaque
  state_current_account_option_spec
  state_recent_account_slice_spec
  version_stack_account_state_current_spec
  : sl_opacity.

Section sender_dipping.
  Context `{Sigma : cpp_logic} {CU : genv}.

  cpp.spec
    (let ctx_ty := monad_chain_context_ty 10 in
     {%cpp_name "monad::can_sender_dip_into_reserve(const monad::Address&, unsigned long, bool, const $ctx_ty&)"}
       .<< Atype (monad_traits_ty 10) >>)
    from reserve_balance_cpp.source as can_sender_dip_into_reserve_spec
    with (
      \arg{senderp: ptr} "sender" (Vref senderp)
      \arg{i: nat} "i" (Vint i)
      \arg{delegated: bool} "sender_is_delegated" (Vbool delegated)
      \arg{ctxp: ptr} "ctx" (Vref ctxp)
      \prepost{qctx ctx} ctxp |-> MonadChainContextR qctx ctx
      \pre{hist: ExtraAcStates} [| historyConsistent ctx hist |]
      \pre{tx: TxWithHdr} [| nth_error (txsWithHdr (cblock ctx)) i = Some tx |]
      \prepost{orig (statep: ptr)} statep |-> StateOriginalR orig
      \prepost{qs} senderp |-> addressR qs (sender tx)
      \pre [| (Z.of_nat i < lengthZ (transactions (currentBlock (blocks ctx))))%Z |]
      \pre [| match mapModelLookup orig (sender tx) with
               | Some (_, aps) =>
                   delegated =
                     ((match preTxState aps with
                       | Some am => isDelegationMarker (block.block_account_code (coreAc am))
                       | None => false
                       end) && asbool (sender tx ∉ undels tx.1.2))
                     || asbool (sender tx ∈ dels tx.1.2)
               | None => False
               end |]
      \post{retb: bool} [Vbool retb]
      [| forall preTxState: StateOfAccounts,
          satisfiesAssumptions' true orig preTxState ->
             retb = isAllowedToEmpty 3 (preTxState, hist) [] tx |]
    ).
End sender_dipping.

Section reserve_threshold.
  Context `{Sigma : cpp_logic} {CU : genv}.

  (* Reading the original balance records an equality assumption, regardless
     of which threshold branch is taken. The returned threshold is unchanged. *)
  cpp.spec (dipped_into_reserve_lam .:: Nop function_qualifiers.Nc OOCall [])
    from reserve_balance_cpp.source as dipped_into_reserve_lam_call_spec
    with (fun this : ptr =>
      \prepost{addrp statep senderp gas_feesp}
        this |-> DippedIntoReserveLambdaR addrp statep senderp gas_feesp
      \prepost{qaddr addr} addrp |-> addressR qaddr addr
      \prepost{qsender sender} senderp |-> addressR qsender sender
      \prepost{qfee gas_fees} gas_feesp |-> u256R qfee gas_fees
      \prepost statep |-> structR "monad::State" 1$m
      \pre{orig} statep |-> StateOriginalR orig
      \pre [| is_Some (mapModelLookup orig addr) |]
      \prepost{preBlockState qb bs (bsp : ptr)}
        statep ,, o_field CU "monad::State::block_state_"
          |-> refR<"monad::BlockState"> 1$m bsp
        ** bsp |-> BlockState.Rfrag preBlockState qb bs
      \post{retp : ptr} [Vptr retp]
        retp |-> optional_specs.optionR u256t u256R 1
          (reserve_violation_threshold_model orig addr sender gas_fees)
        ** statep |-> StateOriginalR
          (update_assum_exactness_at addr exact_balance_update orig)
    ).
End reserve_threshold.

Section debit_constraint.
  Context `{Sigma : cpp_logic} {CU : genv}.

  (* This is the previous check_min_balance slice contract, for the production
     method that now includes its helper body. Current values are preserved;
     only the original account's recorded balance constraint changes. *)
  cpp.spec "monad::State::record_balance_constraint_for_debit(const monad::Address&, const monad::uint256_t&)"
    from state_cpp.source as state_record_balance_constraint_for_debit_spec
    with (fun this : ptr =>
      \arg{addrp : ptr} "address" (Vref addrp)
      \arg{valuep : ptr} "debit" (Vref valuep)
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
                (map (fun '(a, (p, _)) => (a, p)) orig)
      \prepost{preBlockState bs qb (bsp : ptr)}
        this ,, o_field CU "monad::State::block_state_"
          |-> refR<"monad::BlockState"> 1$m bsp
        ** bsp |-> BlockState.Rfrag preBlockState qb bs
      \prepost{qcur cur} StateCurrentLookupR this qcur addr cur
      \pre [|
        match mapModelLookup cur addr with
        | Some _ => is_Some (mapModelLookup orig addr)
        | None => True
        end |]
      \prepost this |-> structR "monad::State" 1$m
      \post{retb : bool} [Vbool retb]
        [| match mapModelLookup cur addr with
           | Some (_, cur_stack) =>
               retb = check_min_balance_ok
                 (current_balance_pessimistic_model_stack cur_stack) value
           | None => True
           end |]
        ** Exists orig_final loc orig_state acct,
          this ,, o_field CU "monad::State::original_"
            |-> AnkerMapPayloadsR "monad::Address" "monad::OriginalAccountState"
                  addressR OriginalAccountStateR 1
                  (check_min_balance_update_model orig_final addr acct value)
          ** this ,, o_field CU "monad::State::original_"
            |-> AnkerMapSpineR "monad::Address" "monad::OriginalAccountState"
                  addressToN addressR 1
                  (map (fun '(a, (p, _)) => (a, p))
                    (check_min_balance_update_model orig_final addr acct value))
          ** [| state_original_account_state_post
                  orig addr orig_final loc orig_state |]
          ** [| acct = check_min_balance_recent_account_model cur addr orig_state |]
          ** [| retb = check_min_balance_ok (balanceOfAccount acct) value |]
    ).
End debit_constraint.

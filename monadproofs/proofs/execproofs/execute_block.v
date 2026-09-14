Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.optional_specs.
Require Import monad.proofs.libspecs.fiber_specs.
Require Import monad.proofs.libspecs.vector_compat.
Import optional_specs.
Import fiber_specs.
Import vector_compat.
Require Import monad.proofs.reservebal.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import skylabs.auto.invariants.
Require Import skylabs.auto.cpp.proof.

Require Import skylabs.auto.cpp.tactics4.
Require Import monad.asts.exb.
Require Import monad.proofs.exec_specs.
Require Import skylabs.auto.cpp.prelude.proof.
Require Import skylabs.brick.libstdcpp.shared_ptr.specs.
Open Scope Z_scope.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
           (*   hh = @has_own_monpred thread_info _Σ fracR (@cinv_inG _Σ (@cpp_has_cinv thread_info _Σ Sigma)) *)
  Context  {MODd : exb.source ⊧ CU}.

  Set Nested Proofs Allowed.
  Set Printing Coercions.

  (*
  cpp.spec (Nscoped 
              (Nscoped (Ninst "monad::execute_transactions(const monad::Block&, monad::fiber::PriorityPool&, const monad::Chain&, const monad::BlockHashBuffer&, monad::BlockState &)" [Avalue (Eint 11 "enum evmc_revision")]) (Nanon 0)) (Ndtor))  as exlamdestr inline.
   *)


  #[global] Instance sharedR_typeptr_observe ety (p:ptr) q base (size: N) (sizeStaticallyKnown:bool)
      : Observe (type_ptr ((Tnamed ("std::span".<< Atype ety, Avalue (Eint (if sizeStaticallyKnown then size else 2^64-1) "unsigned long") >>) ))p ) (p|-> SpanRbase ety q base size sizeStaticallyKnown).
  Proof. Admitted.
  Definition observeSharedType  a b c d e f:= @observe_fwd _ _ _ (sharedR_typeptr_observe a b c d e f).
  Hint Resolve @observeSharedType: sl_opacity.


  Ltac slauto := (slautot ltac:(autorewrite with syntactic (*equiv iff slbwd *); (*try rewrite left_id; *) (*try solveRefereceTo; *) try autounfold with unfold; try Forward.forward_reason; try Forward.rwHyps (*; try optionSomeBig;  try instOptionR*))); try iPureIntro.

  Hint Unfold SpanR BlockR VectorR : unfold.
  Hint Rewrite @lengthN_map: syntactic.

  Context {hf:fracG () _Σ}.

  Require Import skylabs.auto.cpp.hints.array.

  
  cpp.spec "boost::fibers::promise<void>::promise()" as promise_ctor with(fun (this:ptr) =>
    \pre{P:mpred} emp
    \post Exists g:gname, this |->  PromiseR g P).

  #[global] Instance promiseR_observe (p:ptr) a b
      : Observe (type_ptr "boost::fibers::promise<void>" p) (p |-> PromiseR a b).
  Proof. Admitted.
  
  Definition observePromiseR  p a b := @observe_fwd _ _ _ (promiseR_observe p a b).
  Hint Resolve @observePromiseR: sl_opacity.


  (** ** Uniform construction, then per-element resources

      The removed indexed experiment ([aggregate_array_const_CG]) generalized
      upstream [aggregate_array_const_C]: instead of obtaining the same logical
      representation for every element, it let construction of element [i]
      produce a representation depending on [i]. The C++ constructor expression
      was unchanged. For a promise or semaphore array, the varying parameter
      could describe the resource transferred or protected at that position.

      The later approach below does not need index-dependent array construction.
      It initializes every promise with the same placeholder resource [emp],
      using ordinary array initialization, then assigns the per-transaction
      resources with:
[[
  rewrite -> (logicallInitPromiseArray2 promisedRec); [| arith_solve].
]]
      This separates constructing the C++ objects from configuring their logical
      synchronization protocol. Changing these parameters requires a justified
      resource-setup lemma; it is not arbitrary relabeling of ownership.
      [logicallInitPromiseArray2] is still admitted in this abandoned proof.

      The separately removed [aggregate_array_const_CI] was not the indexed
      generalization: it adapted a constructor annotated with an incomplete
      array type to initialization of a complete array. *)

  Disable Notation "::wpPRᵢ" (all).
Instance XXX2 :
  semantic_const.SemConst_wp_initialize "boost::fibers::promise<void>" (Econstructor "boost::fibers::promise<void>::promise()" [] "boost::fibers::promise<void>") ext.source promise_ctor emp tt (fun i => Exists g,  PromiseR g emp).
  Proof using.
    constructor.
    go. iExists emp. simpl. go.
  Qed.
Instance XXX3 :
  semantic_const.SemConst_wp_initialize "boost::fibers::promise<void>" (Econstructor "boost::fibers::promise<void>::promise()" [] "boost::fibers::promise<void>") exb.source promise_ctor emp tt (fun i => Exists g,  PromiseR g emp).
  Proof using.
    constructor.
    go. iExists emp. simpl. go.
  Qed.

    Lemma logicallInitPromiseArray (preci : nat -> mpred) (base: ptr) len:
      (base 
      |-> arrayLR "boost::fibers::promise<void>" 0 len
            (λ _ : (), ∃ g0 : gname, PromiseR g0 emp) (replicateZ len ()))
        |-- Exists (prIds: nat -> gname), base |->  parrayR (Tnamed "boost::fibers::promise<void>") (fun i _ => PromiseR (prIds i) (preci i)) (replicateZ len ()).
    Proof using. Admitted.

    Definition promisedRec (i:nat) preBlockState block (block_hash_bufferp chainp block_statep vectorbase blockp : ptr) qbuf buf  qchain qs  qb  qf g chain : mpred:=
      match execTxs preBlockState (take i (txsWithHdr block)) with
      | None => emp (* TODO: return all ownership. just copy what is left in proofs *)
      | Some (actual_final_state, receipts) =>
    ((_global "monad::results" |-> arrayR oResultT (fun r => optional_specs.optionR resultT (fun _ => ResultSuccessR ReceiptR) 1$m (Some r)) receipts)
     ** ([∗ list] _ ∈ (take i (transactions block)),  (block_hash_bufferp |-> BlockHashBufferR (qbuf*/(N_to_Qp (1+ lengthN (transactions block)))) buf))
     ** ([∗ list] _ ∈ (take i (transactions block)),  (chainp |-> ChainR (qchain*/(N_to_Qp (1+ lengthN (transactions block)))) chain))
     ** _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR qs (Some (sender t)))
            (take i (txsWithHdr block))

     ** (_global "monad::promises" |->
            parrayR
              (Tnamed "boost::fibers::promise<void>")
              (fun i t => PromiseUnusableR)
              ((map (fun _ => ()) (take i (transactions block)))))
     ** ([∗ list] _ ∈ (take i (transactions block)),  blockp ,, o_field CU (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "Block")) (Nid "header"))
      |-> BheaderR (qb*/(N_to_Qp (1+ lengthN (transactions block)))) (header block))
     ** ([∗ list] _ ∈ (take i (transactions block)),  (block_statep |-> BlockState.Rfrag preBlockState (qf*/(N_to_Qp (1+ lengthN (transactions block)))) g))
     **  vectorbase
          |-> arrayR (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))) (λ t0 : Transaction, TransactionR qb t0)
          (take i (transactions block)))
      ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state
      end.
    
    Ltac renArrayBase ty b :=
    IPM.perm_left ltac:(fun L _ =>
                          match L with
                          | ?base |-> arrayR ty _  _ => rename base into b
                          end
                       ).
    Definition promiseArrPiece (promisedReci: nat->mpred) (prIds: nat -> gname) (len: Z) (i:nat) : Rep :=
      if (bool_decide (i<len)) then
         .[ "boost::fibers::promise<void>" ! (Z.of_nat i) ] |->
                (type_ptrR "boost::fibers::promise<void>" ** (PromiseR (prIds i) (promisedReci i)))
      else
        emp.
    Lemma logicallInitPromiseArray2 (preci : nat -> mpred) (base: ptr) (len:Z):
      (len < 2^32) ->
      (base 
         |-> arrayLR "boost::fibers::promise<void>" 0 len
         (λ _ : (), ∃ g0 : gname, PromiseR g0 emp) (replicateZ len ()))
        |-- Exists (prIds: nat -> gname),
          base |-> promiseArrPiece preci prIds len 0 
           ** ([∗ list] pieceid ∈ allButFirstPieceId,  base |-> promiseArrPiece preci prIds len pieceid).
    Proof. Admitted.
    Ltac glob_def_find :=
      erewrite glob_def_Struct;[ | eassumption|];[| reflexivity].
    #[global] Instance lll (Rpiece1 Rpiece2: nat -> Rep) (base: ptr) :
      Learnable
        ([∗ list] pieceid ∈ allButFirstPieceId, base |-> Rpiece1 pieceid)
        ([∗ list] pieceid ∈ allButFirstPieceId, base |-> Rpiece2 pieceid)
        [Rpiece1 = Rpiece2] := ltac:(solve_learnable).
    Ltac solveDynAllocatedR :=
      iExists _,_;
      unfold test.dynAllocatedR;
      go;
      iExists _, _;
      eagerUnifyU;
      go;
      glob_def_find;
      simpl.
    Lemma promiseArrayDealloc promisedRec len prIds:
      ([∗ list] pieceid ∈ allPieceIds, promiseArrPiece promisedRec prIds len pieceid)
     ⊢ anyR (Tarray "boost::fibers::promise<void>" (Z.to_N len)) 1$m.
    Proof using. Admitted.

    Hint Resolve promiseArrayDealloc : pure.

    (*
  #[global] Instance array_incomplete (p:ptr) ty (len:N) {prf: (0<len)}
      : Observe (type_ptr (Tnamed ("std::shared_ptr".<<Atype (Tincomplete_array ty)>>)) p) (type_ptr (Tnamed ("std::shared_ptr".<<Atype (Tarray ty len)>>)) p).
  Proof using. Admitted.
  Definition observeArrInc  a b c d:= @observe_fwd _ _ _ (@array_incomplete a b c d).
  Hint Resolve @observeArrInc: sl_opacity.
*)
    Opaque SharedPtrR.
    Definition arrayR_nil_at X R ty p := @_at_proper _ _ _ p _ _ (@arrayR_nil _ _ _ _ X R ty).
    Definition arnilfwd := [FWD->](@arrayR_nil_at).
    Definition arnilbwd := [BWD->](@arrayR_nil_at).
    Definition parrayR_nil_at X R ty p := @_at_proper _ _ _ p _ _ (@parrayR_nil _ _ _ _ X R ty).
    Definition parnilfwd := [FWD->](@parrayR_nil_at).
    Definition parnilbwd := [BWD->](@parrayR_nil_at).
    Hint Resolve arnilfwd arnilbwd parnilfwd parnilbwd : sl_opacity.
    #[global] Instance llls: LearnEq4 SharedPtrR := ltac:(solve_learnable).

    Hint Unfold txsWithHdr : unfold.
  Lemma prf: 
           verify?[source]  exbt_spec.
  Proof using MODd.
    verify_spec'.
    autounfold with unfold.
    slauto.
    iExists _.
    provePure.
    {
      erewrite glob_def_Struct; try eauto.
    }

    assert ((lengthN (transactions block) +1) < 2^32)%N as Hln by admit.
(*    assert (16* (lengthN (transactions block) +1) < 2^64 - 1)%N as Hl by lia. *)
    Arith.remove_useless_mod_a.
    go.
    name_locals.
    renArrayBase (Tconst "monad::Transaction") txvbase.
    set (promisedRec (i: nat) :=
      match execTxs preBlockState (take i (txsWithHdr block)) with
      | None => emp (* TODO: return all ownership. just copy what is left in proofs *)
      | Some (actual_final_state, receipts) =>
    ((_global "monad::results" |-> arrayR oResultT (fun r => optional_specs.optionR resultT (fun _ => ResultSuccessR ReceiptR) 1$m (Some r)) receipts)
     ** ([∗ list] _ ∈ (take i (transactions block)),  (block_hash_bufferp |-> BlockHashBufferR (qbuf*/(N_to_Qp (1+ lengthN (transactions block)))) buf))
     ** ([∗ list] _ ∈ (take i (transactions block)),  (chainp |-> ChainR (qchain*/(N_to_Qp (1+ lengthN (transactions block)))) chain))
     ** _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR qs (Some (sender t)))
            (take i (txsWithHdr block))

     ** (_global "monad::promises" |->
            parrayR
              (Tnamed "boost::fibers::promise<void>")
              (fun i t => PromiseUnusableR)
              ((map (fun _ => ()) (take i (transactions block)))))
     ** ([∗ list] _ ∈ (take i (transactions block)),  hdrp 
      |-> BheaderR (qblock*/(N_to_Qp (1+ lengthN (transactions block)))) (header block))
     ** ([∗ list] _ ∈ (take i (transactions block)),  (block_statep |-> BlockState.Rfrag preBlockState (qf*/(N_to_Qp (1+ lengthN (transactions block)))) g))
     **  txvbase
          |-> arrayR "const monad::Transaction" (λ t0 : Transaction, TransactionR qblock t0)
          (take i (transactions block)))
      (* TODO: add the other arrays *)
      ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state
        end).

    Set Printing Coercions.
    autorewrite with syntactic.

    rewrite -> (logicallInitPromiseArray2 promisedRec);[| arith_solve].
    go.
    solveDynAllocatedR.
    go.
    normalize_ptrs.
    go.
    normalize_ptrs.
    unfold promiseArrPiece.
    unfold promiseArrPiece.
    resolveDecide lia.
    go.
    normalize_ptrs.
    Lemma sharePromise2 g P:  PromiseR g P -|- PromiseConsumerR g P **  PromiseProducerR g P.
    Proof using. rewrite sharePromise. iSplit; go. Qed.
    
    Definition sharePromiseC := [CANCEL] sharePromise.
    Definition sharePromiseC2 := [CANCEL] sharePromise2.
    Hint Resolve sharePromiseC sharePromiseC2: sl_opacity.
    #[global] Instance lll2 g1 g2 P1 P2: Learnable (PromiseR g1 P1) (PromiseConsumerR g2 P2) [g1=g2; P1=P2] := ltac:(solve_learnable).
    #[global] Instance lll3 g1 g2 P1 P2: Learnable (PromiseR g1 P1) (PromiseProducerR g2 P2) [g1=g2; P1=P2] := ltac:(solve_learnable).
    go.
    erewrite glob_def_Struct;[ | eassumption|].
    2:{ unfold resultT.
        vm_compute.
        }
    [| reflexivity].
  
  Abort.

  Lemma prf: 
           verify?[source]  exbb_spec.
  Proof using MODd.
    verify_spec'.
    autounfold with unfold.
    slauto.
  Abort.


End with_Sigma.

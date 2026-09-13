Set Default Goal Selector "!".

(*Require Import monad.proofs.evmopsem. *)
Require Import monad.proofs.misc.
(*Require Import skylabs.hw_models.utils. *)
(* Require Import skylabs.auto.cpp.tactics4. *)
Require Import elpi.apps.derive.derive.
Require Import Lens.Lens.
Require Import Lens.Elpi.Elpi.
Import LensNotations.
#[local] Open Scope lens_scope.
Require Import EVMOpSem.block.

Definition w256 := N.
Definition EvmAddr := N.

Definition tsender (t:block.transaction) : EvmAddr := Z.to_N (word160.word160ToInteger (block.tr_from t)).

Record Indices :=
  {
    block_index: N;
    tx_index: N;
  }.


Record AccountM : Type :=
  {
    coreAc: block.block_account;
    incarnation: Indices; (* the blocknumber, tx number when this "incarnation" of the account was created. the EVM semantics does not really track this but we do to help reason about concurrent execution of transactions. This seems to be useful mainly in caching to avoid confusing different incarnations of the same address *)
    relevantKeys: list N; (* only the storage keys listed here are relevant. for assumptions, there are the only read keysk. for updates, these are the only updated keys. In C++, storage maps typically will have only these keys.
    must be [] if coreState is []*)
    balance : N (* one one in coreAc is of type word256 which is harder to use. instead, we use N and ensure the operations never overflow, e.g. by modding or capping. some assumptions in reserve balance proofs require capping to 2^256. in practice, the distinction is moot unless the money suppy blows up *)
  }.

(* Cryptographic code hash (Keccak-256), modeled abstractly. *)
Axiom keccak256_program : evm.program -> N.

Definition code_hash_of_program
           (pr: EVMOpSem.evm.program)
  : Corelib.Numbers.BinNums.N :=
  keccak256_program pr.

(* Delegation marker bytecode has fixed length 3 + 20. *)
Definition delegation_indicator_size : Z := 23%Z.
Parameter delegation_marker_prefix : evm.program -> bool.

Definition isDelegationMarker (p: evm.program) : bool :=
  (Z.eqb (EVMOpSem.evm.program_length p) delegation_indicator_size)
    && delegation_marker_prefix p.

(* Delegation is represented by account code marker (single delegate target). *)
Definition delegatedTo (a: AccountM) : option EvmAddr :=
  if isDelegationMarker (block.block_account_code (coreAc a))
  then Some 0%N
  else None.

Record TxResult :=
  {
    gas_used: N;
    gas_refund: N;
    logs: list evm.log_entry;
    (* sender : EvmAddr *)
  }.

Record BlockHeader :={
    base_fee_per_gas: option w256;
    number: N;
    beneficiary: EvmAddr;
    timestamp: N;
    }.

#[only(lens)] derive block.block_account.
 #[only(lens)] derive AccountM.
 #[only(lens)] derive BlockHeader.

 Definition w256_to_Z (w: EVMOpSem.keccak.w256) : Z :=
  EVMOpSem.Zdigits.binary_value 256 w.

Definition w256_to_N (w: EVMOpSem.keccak.w256) : N :=
  Z.to_N (w256_to_Z w).

Definition Z_to_w256 wnz : EVMOpSem.keccak.w256 := Zdigits.Z_to_binary _ wnz.

Opaque Zdigits.binary_value Zdigits.Z_to_binary.

Definition zbvfun (fz: Z -> Z) (w: keccak.w256): keccak.w256:=
  let wnz := fz (w256_to_Z w) in
  Z_to_w256 wnz.


Definition nbvfun (fz: N -> N) (w: keccak.w256): keccak.w256:=
  let wnz := fz (w256_to_N w) in
  Z_to_w256 (Z.of_N wnz).


Definition zbvlens {A:Type} (l: Lens A A keccak.w256 keccak.w256): Lens A A Z Z :=
  {| view := fun a : A=> w256_to_Z (a .^ l);
    Lens.over := fun (fz : Z -> Z) (a : A)=> (l %= zbvfun fz) a |}.

Definition nbvlens {A:Type} (l: Lens A A keccak.w256 keccak.w256): Lens A A N N :=
  {| view := fun a : A => w256_to_N (a .^ l);
    Lens.over := fun (fz : N -> N) (a : A)=> (l %= nbvfun fz) a |}.


(*
Definition _balance : Lens AccountM AccountM Z Z:=
  zbvlens (_coreAc .@ _block_account_balance).
 *)

Definition _balanceN : Lens AccountM AccountM N N :=
  nbvlens (_coreAc .@ _block_account_balance).

(*
#[global] Instance inh : Inhabited AccountM := populate dummyAc.
Definition updateBalanceOfAc (s: evm.GlobalState) (addr: EvmAddr) (upd: N -> N) : evm.GlobalState :=
  <[ addr :=  (s !!! addr) &: _balance %= upd ]> s.


Lemma def0:
  w256_to_N keccak.w256_default = 0%N.
Proof using.
  reflexivity.
Qed.


Lemma balanceOfUpd s ac f acp:
  balanceOfAc (updateBalanceOfAc s ac f) acp = if (bool_decide (ac=acp)) then f (balanceOfAc s ac) else (balanceOfAc s acp).
Proof.
  simpl.
  unfold updateBalanceOfAc.
  unfold balanceOfAc.
  autorewrite with syntactic.
  rewrite lookup_insert_iff;[| exact dummyAc].
  case_bool_decide;  auto.
  unfold lookup_total.
  unfold fin_maps.map_lookup_total.
  unfold default.
  unfold evm.account_state.
  case_match; auto.
  2:{
    setoid_rewrite H0.
    reflexivity.
  }
  {
    setoid_rewrite H0.
    unfold id.
    destruct a.
    reflexivity.
  }
Qed.
*)

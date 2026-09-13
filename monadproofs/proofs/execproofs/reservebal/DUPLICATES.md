Reserve-balance lemma wrapper inventory

This directory has been regrouped by theme:

- `core_lemmas.v`
- `update_exactness_lemmas.v`
- `non_sender_lemmas.v`
- `sender_update_helpers.v`
- `sender_rewrite_lemmas.v`
- `sender_low_balance_lemmas.v`
- `sender_sufficient_balance_lemmas.v`

The remaining deliberate duplicates are thin wrappers kept only to avoid
touching current callers. These are candidates to inline at usage sites later.

Wrappers over core lemmas

- `update_exactness_lemmas.map_key_ptr_update_assum_exactness_at`
  - exact wrapper over `core_lemmas.map_key_ptr_update_assum_exactness_at`
- `update_exactness_lemmas.map_key_ptr_update_assum_exactness_map`
  - exact wrapper over `core_lemmas.map_key_ptr_update_assum_exactness_map`
- `update_exactness_lemmas.map_key_ptr_check_min_original_balance_update`
  - exact wrapper over `core_lemmas.map_key_ptr_check_min_original_balance_update`

Compatibility wrappers

- `non_sender_lemmas.nonSenderBalanceInsuff`
  - compatibility wrapper over `nonSenderBalanceInsuff_aug`
  - current notable caller: `reserve_balance.v`

Rewrite wrappers

- `sender_rewrite_lemmas.rwlem2_rewrite`
  - thin wrapper over:
    - `rwlem2`
    - `mapModelLookup_match_preTxState_update_assum_exactness_at_rw`
  - current notable caller: `reserve_balance.v`

Shared proof chunks already factored out

- sender fee/max-fee setup:
  - `tx_base_fee_per_gas_eq_of_txidx`
  - `gas_fee_model_lt_2_256_of_validTx_ctx`
  - `maxTxFee_eq_fee_raw_of_validTx_ctx`
  - `maxTxFee_eq_fee_mod_of_validTx_ctx`
- sender insert/update setup:
  - `sender_insert_validModel_twice`
  - `sender_insert_validModel_once`
  - `sender_insert_updates_stricter_once`
  - `sender_check_min_eq_of_lookup`

Potential next inlining/deletion pass

1. Inline the three `map_key_ptr_*` wrappers at call sites that can import or
   qualify `core_lemmas` directly.
2. Inline `nonSenderBalanceInsuff` into its current callers, then delete the
   wrapper in favor of `nonSenderBalanceInsuff_aug`.
3. Inline `rwlem2_rewrite` at its current callers if the extra rewrite step is
   still justified there.

// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/reserve_balance.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/reserve_balance.h>
#include <category/execution/monad/reserve_balance.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/delegation.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>

#include <intx/intx.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <ranges>

unsigned monad_default_max_reserve_balance_mon(enum monad_revision)
{
    return 10;
}

MONAD_ANONYMOUS_NAMESPACE_BEGIN

template <Traits traits>
bool dipped_into_reserve(State &state)
{
    MONAD_ASSERT(state.reserve_balance_tracking_enabled<traits>());
    return state.reserve_balance_has_violation<traits>();
}

template <Traits traits>
constexpr bool reserve_tracking_supported()
{
    if constexpr (!is_monad_trait_v<traits>) {
        return false;
    }
    else {
        return traits::monad_rev() >= MONAD_FOUR;
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

ReserveBalance::ReserveBalance(State *state)
    : state_{state}
{
}

template <Traits traits>
bool ReserveBalance::tracking_enabled() const
{
    if constexpr (reserve_tracking_supported<traits>()) {
        return tracking_context_initialized_;
    }
    else {
        return false;
    }
}

template <Traits traits>
bool ReserveBalance::has_violation() const
{
    if constexpr (reserve_tracking_supported<traits>()) {
        return !failed_.empty();
    }
    else {
        return false;
    }
}

bool ReserveBalance::failed_contains(Address const &address) const
{
    return failed_.contains(address);
}

template <Traits traits>
    requires is_monad_trait_v<traits>
bool ReserveBalance::subject_account(Address const &address)
{
    OriginalAccountState &orig_state = state_->original_account_state(address);
    bytes32_t const effective_code_hash =
        [](State &state, OriginalAccountState &original, Address const &acct) {
            if constexpr (traits::monad_rev() >= MONAD_EIGHT) {
                return state.get_code_hash(acct);
            }
            else {
                return original.get_code_hash();
            }
        }(*state_, orig_state, address);
    if (effective_code_hash == NULL_HASH) {
        return true;
    }
    return state_->is_delegated(effective_code_hash);
}

template <Traits traits>
    requires is_monad_trait_v<traits>
uint256_t ReserveBalance::pretx_reserve(Address const &address)
{
    uint256_t const max_reserve = get_max_reserve<traits>(address);
    return std::min(max_reserve, state_->get_original_balance(address));
}

template <Traits traits>
    requires is_monad_trait_v<traits>
void ReserveBalance::update_violation_status(Address const &address)
{
    if (!tracking_context_initialized_) {
        return;
    }

    auto &violation_threshold = violation_thresholds_[address];
    if (!violation_threshold.has_value()) {
        if (!subject_account<traits>(address)) {
            violation_threshold = uint256_t{0};
            failed_.erase(address);
            return;
        }

        uint256_t reserve = pretx_reserve<traits>(address);
        if (address == sender_) {
            if (sender_can_dip_) {
                violation_threshold = uint256_t{0};
                failed_.erase(address);
                return;
            }
            MONAD_ASSERT_THROW(
                sender_gas_fees_ <= reserve,
                "gas fee greater than reserve for non-dipping transaction");
            reserve = reserve - sender_gas_fees_;
        }
        violation_threshold = reserve;
    }

    if (*violation_threshold == 0) {
        failed_.erase(address);
        return;
    }

    if (state_->get_balance(address) < *violation_threshold) {
        failed_.insert(address);
    }
    else {
        failed_.erase(address);
    }
}

template <Traits traits>
void ReserveBalance::on_credit(Address const &address)
{
    if constexpr (reserve_tracking_supported<traits>()) {
        if (!tracking_context_initialized_) {
            return;
        }
        if (failed_.contains(address)) {
            update_violation_status<traits>(address);
        }
    }
}

template <Traits traits>
void ReserveBalance::on_debit(Address const &address)
{
    if constexpr (reserve_tracking_supported<traits>()) {
        update_violation_status<traits>(address);
    }
}

template <Traits traits>
void ReserveBalance::on_pop_reject(FailedSet const &accounts)
{
    if constexpr (reserve_tracking_supported<traits>()) {
        if (!tracking_context_initialized_) {
            return;
        }
        for (auto const &dirty_address : accounts) {
            violation_thresholds_[dirty_address].reset();
            update_violation_status<traits>(dirty_address);
        }
    }
}

template <Traits traits>
void ReserveBalance::on_set_code(
    Address const &address, byte_string_view const code)
{
    if constexpr (reserve_tracking_supported<traits>()) {
        if constexpr (traits::monad_rev() >= MONAD_EIGHT) {
            if (!tracking_context_initialized_) {
                return;
            }
            auto &violation_threshold = violation_thresholds_[address];
            if (!vm::evm::is_delegated({code.data(), code.size()})) {
                violation_threshold = uint256_t{0};
                failed_.erase(address);
                return;
            }
            violation_threshold.reset();
            update_violation_status<traits>(address);
        }
    }
}

template <Traits traits>
void ReserveBalance::init_from_tx(
    Address const &sender, Transaction const &tx,
    std::optional<uint256_t> const &base_fee_per_gas, uint64_t i,
    ChainContext<traits> const &ctx)
{
    if constexpr (!reserve_tracking_supported<traits>()) {
        tracking_context_initialized_ = false;
        sender_ = {};
        sender_gas_fees_ = 0;
        sender_can_dip_ = false;
        failed_.clear();
        violation_thresholds_.clear();
        return;
    }

    MONAD_ASSERT(i < ctx.senders.size());
    MONAD_ASSERT(i < ctx.authorities.size());
    MONAD_ASSERT(ctx.senders.size() == ctx.authorities.size());
    bytes32_t const sender_code_hash = [](State &state,
                                          Address const &sender_address) {
        if constexpr (traits::monad_rev() >= MONAD_EIGHT) {
            return state.get_code_hash(sender_address);
        }
        else {
            return state.original_account_state(sender_address).get_code_hash();
        }
    }(*state_, sender);
    bool const sender_can_dip = can_sender_dip_into_reserve<traits>(
        sender, i, state_->is_delegated(sender_code_hash), ctx);
    tracking_context_initialized_ = true;
    sender_ = sender;
    sender_gas_fees_ = uint256_t{tx.gas_limit} *
                       gas_price<traits>(tx, base_fee_per_gas.value_or(0));
    sender_can_dip_ = sender_can_dip;
    failed_.clear();
    violation_thresholds_.clear();
}

EXPLICIT_MONAD_TRAITS_MEMBER(ReserveBalance::init_from_tx);
EXPLICIT_TRAITS_MEMBER(ReserveBalance::tracking_enabled);
EXPLICIT_TRAITS_MEMBER(ReserveBalance::has_violation);
EXPLICIT_TRAITS_MEMBER(ReserveBalance::on_credit);
EXPLICIT_TRAITS_MEMBER(ReserveBalance::on_debit);
EXPLICIT_TRAITS_MEMBER(ReserveBalance::on_pop_reject);
EXPLICIT_TRAITS_MEMBER(ReserveBalance::on_set_code);

template <Traits traits>
bool revert_transaction(State &state)
{
    if constexpr (traits::monad_rev() >= MONAD_FOUR) {
        return dipped_into_reserve<traits>(state);
    }
    else if constexpr (traits::monad_rev() >= MONAD_ZERO) {
        return false;
    }
}

EXPLICIT_MONAD_TRAITS(revert_transaction);

template <Traits traits>
    requires is_monad_trait_v<traits>
bool can_sender_dip_into_reserve(
    Address const &sender, uint64_t const i, bool const sender_is_delegated,
    ChainContext<traits> const &ctx)
{
    if (sender_is_delegated) { // delegated accounts cannot dip
        return false;
    }

    // check pending blocks
    if (ctx.grandparent_senders_and_authorities.contains(sender) ||
        ctx.parent_senders_and_authorities.contains(sender)) {
        return false;
    }

    // check current block
    if (ctx.senders_and_authorities.contains(sender)) {
        for (size_t j = 0; j <= i; ++j) {
            if (j < i && sender == ctx.senders.at(j)) {
                return false;
            }
            if (std::ranges::contains(ctx.authorities.at(j), sender)) {
                return false;
            }
        }
    }

    return true; // Allow dipping into reserve if no restrictions found
}

EXPLICIT_MONAD_TRAITS(can_sender_dip_into_reserve);

template <Traits traits>
uint256_t get_max_reserve(Address const &)
{
    // TODO: implement precompile (support reading from orig)
    constexpr uint256_t WEI_PER_MON{1000000000000000000};
    return uint256_t{
               monad_default_max_reserve_balance_mon(traits::monad_rev())} *
           WEI_PER_MON;
}

EXPLICIT_MONAD_TRAITS(get_max_reserve);

MONAD_NAMESPACE_END

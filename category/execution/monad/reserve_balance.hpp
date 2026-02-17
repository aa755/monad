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

#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>

#include <evmc/evmc.h>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

class AccountState;
class OriginalAccountState;
class State;
struct Transaction;

class ReserveBalance
{
    using FailedSet = ankerl::unordered_dense::segmented_set<Address>;
    using ViolationThresholdMap = ankerl::unordered_dense::segmented_map<
        Address, std::optional<uint256_t>>;

    State *state_;
    bool tracking_context_initialized_{false};
    Address sender_{};
    uint256_t sender_gas_fees_{0};
    bool sender_can_dip_{false};
    FailedSet failed_{};
    ViolationThresholdMap violation_thresholds_{};

    template <Traits traits>
        requires is_monad_trait_v<traits>
    bool subject_account(Address const &);
    template <Traits traits>
        requires is_monad_trait_v<traits>
    uint256_t pretx_reserve(Address const &);
    template <Traits traits>
        requires is_monad_trait_v<traits>
    void update_violation_status(Address const &);

public:
    explicit ReserveBalance(State *state);

    template <Traits traits>
    bool tracking_enabled() const;
    template <Traits traits>
    bool has_violation() const;

    bool failed_contains(Address const &address) const;

    template <Traits traits>
    void on_credit(Address const &);
    template <Traits traits>
    void on_debit(Address const &);

    template <Traits traits>
    void on_pop_reject(FailedSet const &accounts);

    template <Traits traits>
    void on_set_code(Address const &address, byte_string_view const code);

    template <Traits traits>
    void init_from_tx(
        Address const &sender, Transaction const &tx,
        std::optional<uint256_t> const &base_fee_per_gas, uint64_t i,
        ChainContext<traits> const &ctx);
};

template <Traits traits>
    requires is_monad_trait_v<traits>
bool can_sender_dip_into_reserve(
    Address const &sender, uint64_t i, bool sender_is_delegated,
    ChainContext<traits> const &);

template <Traits traits>
uint256_t get_max_reserve(Address const &);

MONAD_NAMESPACE_END

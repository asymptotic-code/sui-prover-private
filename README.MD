# Sui Prover

A tool for verifying the correctness of Move smart contracts on the Sui blockchain. Based on the Boogie verification engine and the Z3 SMT solver.

Go to [Sui Prover Documentation](https://info.asymptotic.tech/sui-prover) for more information.

## Quick Start

### Install from brew

```bash
brew install asymptotic-code/sui-prover/sui-prover
```

## Basic Usage

Write specifications for your smart contract that the Sui Prover will verify.

### Specification Structure

```rust
#[spec(prove)]
fun function_spec<T>(args): ReturnType {
    // Preconditions on arguments
    
    let result = original_function(args);
    
    // Postconditions that must hold
    
    result
}
```

### Example

Consider a simplified LP (Liquidity Pool) smart contract:

```rust
module amm::simple_lp;

use sui::balance::{Balance, Supply, zero};

public struct LP<phantom T> has drop {}

public struct Pool<phantom T> has store {
    balance: Balance<T>,
    shares: Supply<LP<T>>,
}

public fun withdraw<T>(pool: &mut Pool<T>, shares_in: Balance<LP<T>>): Balance<T> {
    if (shares_in.value() == 0) {
        shares_in.destroy_zero();
        return zero()
    };

    let balance = pool.balance.value();
    let shares = pool.shares.supply_value();

    let balance_to_withdraw = (((shares_in.value() as u128) * (balance as u128)) / (shares as u128)) as u64;

    pool.shares.decrease_supply(shares_in);
    pool.balance.split(balance_to_withdraw)
}
```

### Example Specification

A specification to verify that the price of a share doesn't decrease when withdrawing funds:

```rust
#[spec(prove)]
fun withdraw_spec<T>(pool: &mut Pool<T>, shares_in: Balance<LP<T>>): Balance<T> {
    requires(shares_in.value() <= pool.shares.supply_value());

    let old_pool = clone!(pool);

    let result = withdraw(pool, shares_in);

    let old_balance = old_pool.balance.value().to_int();
    let new_balance = pool.balance.value().to_int();

    let old_shares = cloned_pool.shares.supply_value().to_int();
    let new_shares = pool.shares.supply_value().to_int();

    ensures(new_shares.mul(old_balance).lte(old_shares.mul(new_balance)));

    result
}
```

## Running the Sui Prover

Run from the `Move.toml` directory:

```bash
sui-prover
```

### Generate Lean

Select the Lean backend and use `--generate-only` to translate the package
without invoking Lean:

```bash
sui-prover --backend lean --generate-only
```

You can run the command from another directory by passing the Move package
path explicitly:

```bash
sui-prover --backend lean --generate-only --path /path/to/move/package
```

The generated Lean project, including its `lakefile.lean`, is written to the
package's `output/` directory. To generate the project and type-check it with
Lake in one step, omit `--generate-only` and ensure `lake` is on `PATH`:

```bash
sui-prover --backend lean
```

When developing against a local Sui checkout, point the prover at its framework
packages and avoid refreshing git dependencies:

```bash
SUI_PROVER_FRAMEWORK_PATH=/path/to/sui/crates/sui-framework/packages \
  sui-prover --backend lean --generate-only --skip-fetch-latest-git-deps \
  --path /path/to/move/package
```

From this repository, replace `sui-prover` in the examples with
`cargo run -p sui-prover --`.

## Claude Code Integration

Install the Sui Prover skill for [Claude Code](https://docs.anthropic.com/en/docs/claude-code) to get AI-assisted specification writing, verification debugging, and prover guidance.

Add the plugin source:
```
/plugin marketplace add asymptotic-code/sui-prover
```

Install the plugin:
```
/plugin install sui-prover@sui-prover
```

Once installed, Claude Code can help you write specifications, run the prover, and debug verification failures using the `/sui-prover` command.

## See Also

[Sui Prover Documentation](https://info.asymptotic.tech/sui-prover)

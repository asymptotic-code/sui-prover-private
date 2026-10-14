# sui-lean

The Lean 4 backend of the Sui Prover. `sui-lean` translates a Move package and its
specifications into Lean, and checks the proofs of every generated obligation.

## Requirements

- Rust (stable)
- [elan](https://github.com/leanprover/elan) with Lean `v4.32.2`

## Build

From this directory, which is its own Cargo workspace:

```bash
cargo build --release --locked -p sui-lean
```

The binary is `sui-lean/target/release/sui-lean`. It locates its Lean model library and the
vendored Lean dependencies relative to this checkout, so keep the checkout in place.

## Usage

From a Move package's repository, generate the Lean project, rebuild it from scratch and
audit every proof obligation:

```bash
sui-lean -p <path to the specs package> --new-pipeline --audit-proofs --audit-clean-room
```

Results are written to `<package>/output/proof_status.toml`.

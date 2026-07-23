# Lean and Boogie backend comparison

This package sends the same Move specifications to either Sui Prover backend.
Run the commands from the repository root.

```powershell
# SMT verification through Boogie and Z3
cargo run -p sui-prover -- --path examples/backend-comparison --backend boogie

# Generate Lean, compile the generated semantics, and check the hand-written proofs
cargo run -p sui-prover -- --path examples/backend-comparison --backend lean
```

The Boogie backend requires `BOOGIE_EXE` and `Z3_EXE` to name installed
executables. For example, in PowerShell:

```powershell
$env:BOOGIE_EXE = "C:\path\to\boogie.exe"
$env:Z3_EXE = "C:\path\to\z3.exe"
```

The Lean backend writes generated files to `examples/backend-comparison/output/`.
The maintained Lean proofs live in `sources/lean/Proofs/`; generated output is
disposable and is ignored by Git.

Use `--generate-only` to inspect either backend's generated artifacts without
running Boogie or `lake build`.

## Selecting a backend per specification

Use an external `backend` attribute immediately above the specification:

```move
#[ext(backend=b"lean")]
#[spec(prove)]
fun theorem_for_lean(...) { ... }
```

The accepted values are `b"lean"`, `b"boogie"`, and `b"both"`. A missing
attribute defaults to `both`, preserving the behavior of existing packages.
`--backend lean` verifies `lean` and `both` specifications; `--backend boogie`
verifies `boogie` and `both` specifications. Specifications assigned to the
other backend do not produce verification or no-abort jobs. During Lean
generation, explicitly Boogie-owned correctness obligations are emitted as
trusted `axiom` declarations so Lean proofs can compose with Boogie-established
contracts and the trust boundary remains visible to `#print axioms`.

This is separate from `#[spec(..., run_on=b"local" | b"cloud")]`, which chooses
where a Boogie job executes rather than which proof backend owns it. `run_on`
does not accept `lean` or `boogie`; use the `backend` attribute for those.

The specifications cover a conditional result, bounded addition with an exact
abort precondition, and a standard-library `Option` value. Boogie discharges
the Move contracts with SMT. Lean checks the corresponding kernel-checked
theorems in `sources/lean/Proofs/BasicProofs.lean`.

## Lean-only demonstration

`sources/lean_only.move` specifies the elementary number-theory fact that a
square is never congruent to 2 modulo 4. If its backend annotation is
temporarily changed from `b"lean"` to `b"both"`, the current Boogie encoding
times out on this nonlinear modular-arithmetic VC with a 10-second limit:

```powershell
cargo run -p sui-prover -- --path examples/backend-comparison `
  --backend boogie --modules lean_only --timeout 10
```

The corresponding Lean proof establishes the widening and multiplication
bounds and then checks the four possible residues modulo 4:

```powershell
cargo run -p sui-prover -- --path examples/backend-comparison `
  --backend lean
```

The `#[ext(backend=b"lean")]` annotation makes this a real Lean-only proof:
normal Boogie runs skip it, while Lean generates and checks it. Removing that
annotation (or changing it to `b"both"`) exposes the intentionally
Boogie-hostile nonlinear arithmetic VC and reproduces the timeout above.

The package also contains `boogie_only.move`, with a Boogie-only identity
contract and no Lean proof file. It verifies under Boogie; Lean emits its
correctness obligations as explicit axioms. `basic.move` demonstrates both an
explicit `b"both"` contract and contracts with the default behavior.

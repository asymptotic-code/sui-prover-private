import Lake
open Lake DSL

package «lean_demo_proofs» where
  moreLeanArgs := #["--tstack=1048576"]

require auto from git
  "https://github.com/leanprover-community/lean-auto.git" @
  "fcbce0f216e71516e88b784944636da4d28ee780"

lean_lib Prelude where
  srcDir := "output"
  roots := #[`Prelude]
  globs := #[.submodules `Prelude]

@[default_target]
lean_lib MoveStdlib where
  srcDir := "output"
  roots := #[`MoveStdlib]
  globs := #[.submodules `MoveStdlib]

@[default_target]
lean_lib Prover where
  srcDir := "output"
  roots := #[`Prover]
  globs := #[.submodules `Prover]

@[default_target]
lean_lib lean_demo where
  srcDir := "output"
  roots := #[`lean_demo]
  globs := #[.submodules `lean_demo]

@[default_target]
lean_lib Termination where
  srcDir := "output"
  roots := #[`Termination]
  globs := #[.submodules `Termination]

@[default_target]
lean_lib Proofs where
  srcDir := "sources/lean"
  roots := #[`Proofs]
  globs := #[.submodules `Proofs]

@[default_target]
lean_lib Correctness where
  srcDir := "output"
  roots := #[`Correctness]
  globs := #[.submodules `Correctness]

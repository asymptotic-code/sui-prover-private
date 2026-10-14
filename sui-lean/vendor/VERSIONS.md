# Vendored Lean proof automation

All dependencies are the upstream `v4.32.0`-tagged sources below, built
against Lean 4.32.2 (`GENERATED_LEAN_TOOLCHAIN`), and are used as local Lake
path dependencies. Generated projects never fetch them from the network. The
Tag and Commit columns name the upstream release the source came from; they do
not move when the toolchain pin does.

| Directory | Upstream | Tag | Commit | Source tree SHA-256 |
| --- | --- | --- | --- | --- |
| `batteries` | https://github.com/leanprover-community/batteries | `v4.32.0` | `023ce7d62a0531e22a5331e20b587817a80d49ff` | `89cee974f9d29c2d69ae06213486eb6bfb22759c8d59d4a24baffcd2e2dfb720` |
| `aesop` | https://github.com/leanprover-community/aesop | `v4.32.0` | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` | `dd0cbd5eeded70f9d95998a48fa906a3460f8b40cd8d7b21a15503af756bf09f` |
| `lean-auto` | https://github.com/leanprover-community/lean-auto | `v4.32.0` | `fcbce0f216e71516e88b784944636da4d28ee780` | `987229cd4ff1f32413ed9b903bcacaa19b560b89768bbbc7acb6ba6e40fcf19d` |

The source digest is deterministic over relative paths and file or symlink
contents, excluding `.git/` and `.lake/`. Each tree's `lean-toolchain` is one
of those files, so bumping the toolchain pin changes all three digests: a
toolchain migration must update the Source tree SHA-256 column here and the
matching `source_digest` constants in `render/mod.rs`, `sui-lean/src/audit.rs`,
and `foxy/skills/move_summary_with_lean/api.py`. The vendored
`lean-auto/lakefile.lean` disables release-cache fetching, module
precompilation, and the unused Zipperposition download target. Aesop's Lake
metadata points to the adjacent vendored Batteries tree. Foxy uses only
`Auto.Tactic` with an already-installed Z3 binary.

The local SMT process patch sends `exit` and waits after reading a solver
result, avoiding a failed attempt to kill an already exited process on Windows.

//! Prebuilt OLeans for the part of the Lean model bundle that never changes
//! between packages.
//!
//! The renderer copies the bundle into every output as local `lean_lib`s
//! (`Prelude`, and `natives/<X>` promoted to `<X>`), so without a seed every
//! run elaborates the same Prelude / MoveStdlib / Sui / Prover models again.
//! A module is SELF-CONTAINED when its whole import closure stays inside the
//! bundle or the toolchain / vendored libraries; those modules elaborate
//! identically in every output and can be built once (`sui-lean
//! --build-olean-seed`). The rest -- `*Lemmas.lean` companions and the
//! natives that import GENERATED framework modules (`MoveStdlib.MoveOption`,
//! `Sui.Tx_context`, ...) -- depend on per-package pruning and are not seeded.
//!
//! Seeding copies a module's artifacts into an output only when that output
//! has no trace for it yet. Lake still validates every seeded artifact against
//! its own input hashes, so a seed built from a different bundle, or a module
//! a package overlay replaced, is rebuilt rather than trusted: a stale seed
//! costs time, never correctness.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use super::lemma_companions::COMPANION_SUFFIX;
use super::{RenderError, RenderResult};

/// Import roots that resolve outside the bundle to something every output
/// has prebuilt: the toolchain and the vendored proof-automation libraries.
const EXTERNAL_ROOTS: [&str; 7] = ["Init", "Std", "Lean", "Lake", "Batteries", "Aesop", "Auto"];

/// Lake artifact directories under `.lake/build` that hold per-module files.
const ARTIFACT_DIRS: [&str; 2] = ["lib/lean", "ir"];

/// Every module of the bundle, in rendered layout, mapped to its source file.
fn bundle_modules(lemmas_dir: &Path) -> RenderResult<BTreeMap<String, PathBuf>> {
    let mut modules = BTreeMap::new();
    for entry in read_dir(lemmas_dir)? {
        if !entry.is_dir() {
            continue;
        }
        let name = file_name(&entry)?;
        if name == "natives" {
            for native in read_dir(&entry)? {
                if native.is_dir() {
                    let lib = file_name(&native)?;
                    collect_modules(&native, &lib, &mut modules)?;
                }
            }
        } else {
            collect_modules(&entry, &name, &mut modules)?;
        }
    }
    Ok(modules)
}

fn collect_modules(
    dir: &Path,
    prefix: &str,
    out: &mut BTreeMap<String, PathBuf>,
) -> RenderResult<()> {
    for path in read_dir(dir)? {
        let name = file_name(&path)?;
        if path.is_dir() {
            if name != ".lake" && name != ".git" {
                collect_modules(&path, &format!("{prefix}.{name}"), out)?;
            }
        } else if let Some(stem) = name.strip_suffix(".lean") {
            out.insert(format!("{prefix}.{stem}"), path);
        }
    }
    Ok(())
}

fn imports(source: &Path) -> RenderResult<Vec<String>> {
    let text = std::fs::read_to_string(source).map_err(|error| RenderError::Io {
        what: format!("read {}: {error}", source.display()),
    })?;
    let mut out = Vec::new();
    for line in text.lines() {
        let line = line.trim_start();
        let line = line.strip_prefix("public ").unwrap_or(line);
        let line = line.strip_prefix("meta ").unwrap_or(line);
        if let Some(rest) = line.strip_prefix("import ") {
            out.extend(
                rest.split("--")
                    .next()
                    .unwrap_or_default()
                    .split_whitespace()
                    .map(str::to_string),
            );
        }
    }
    Ok(out)
}

/// The bundle modules that can be prebuilt once and reused by every output,
/// sorted. `*Lemmas.lean` companions are never included.
pub fn self_contained_bundle_modules(lemmas_dir: &Path) -> RenderResult<Vec<String>> {
    let modules = bundle_modules(lemmas_dir)?;
    let mut graph: BTreeMap<&str, Vec<String>> = BTreeMap::new();
    for (module, source) in &modules {
        graph.insert(module.as_str(), imports(source)?);
    }
    let mut verdicts: BTreeMap<String, bool> = BTreeMap::new();
    for (module, source) in &modules {
        if source
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.ends_with(COMPANION_SUFFIX))
        {
            verdicts.insert(module.clone(), false);
        }
    }
    let mut result = BTreeSet::new();
    for module in modules.keys() {
        if resolve(module, &graph, &mut verdicts, &mut BTreeSet::new()) {
            result.insert(module.clone());
        }
    }
    Ok(result.into_iter().collect())
}

fn resolve(
    module: &str,
    graph: &BTreeMap<&str, Vec<String>>,
    verdicts: &mut BTreeMap<String, bool>,
    visiting: &mut BTreeSet<String>,
) -> bool {
    if let Some(verdict) = verdicts.get(module) {
        return *verdict;
    }
    let root = module.split('.').next().unwrap_or(module);
    let Some(imports) = graph.get(module) else {
        return EXTERNAL_ROOTS.contains(&root);
    };
    if !visiting.insert(module.to_string()) {
        return false;
    }
    let verdict = imports
        .iter()
        .all(|import| resolve(import, graph, verdicts, visiting));
    visiting.remove(module);
    verdicts.insert(module.to_string(), verdict);
    verdict
}

/// Copy the seed's per-module Lake artifacts into `output_dir/.lake/build`
/// for every module the output has no trace for yet. Returns how many
/// modules were seeded.
pub fn seed_lake_build(seed_dir: &Path, output_dir: &Path) -> RenderResult<usize> {
    let seed_build = seed_dir.join(".lake/build");
    let seed_lib = seed_build.join("lib/lean");
    if !seed_lib.is_dir() {
        return Err(RenderError::Io {
            what: format!(
                "OLean seed {} has no {} -- build it with `sui-lean --build-olean-seed {}`",
                seed_dir.display(),
                seed_lib.display(),
                seed_dir.display()
            ),
        });
    }
    let mut traces = Vec::new();
    collect_files(&seed_lib, &mut traces)?;
    let output_build = output_dir.join(".lake/build");
    let mut seeded = 0;
    for trace in traces {
        let Some(relative) = trace
            .strip_prefix(&seed_lib)
            .ok()
            .filter(|_| trace.extension().is_some_and(|ext| ext == "trace"))
            .map(|path| path.with_extension(""))
        else {
            continue;
        };
        if output_build
            .join("lib/lean")
            .join(&relative)
            .with_extension("trace")
            .exists()
        {
            continue;
        }
        let stem = relative
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| RenderError::Io {
                what: format!("non-UTF-8 seed artifact {}", trace.display()),
            })?
            .to_string();
        for artifact_dir in ARTIFACT_DIRS {
            let source_dir = seed_build
                .join(artifact_dir)
                .join(&relative)
                .with_file_name("");
            if !source_dir.is_dir() {
                continue;
            }
            let target_dir = output_build
                .join(artifact_dir)
                .join(&relative)
                .with_file_name("");
            for source in read_dir(&source_dir)? {
                let name = file_name(&source)?;
                if source.is_file() && name.split('.').next() == Some(stem.as_str()) {
                    std::fs::create_dir_all(&target_dir).map_err(|error| RenderError::Io {
                        what: format!("create_dir_all({}): {error}", target_dir.display()),
                    })?;
                    let target = target_dir.join(&name);
                    std::fs::copy(&source, &target).map_err(|error| RenderError::Io {
                        what: format!("copy {} -> {}: {error}", source.display(), target.display()),
                    })?;
                }
            }
        }
        seeded += 1;
    }
    Ok(seeded)
}

fn collect_files(dir: &Path, out: &mut Vec<PathBuf>) -> RenderResult<()> {
    for path in read_dir(dir)? {
        if path.is_dir() {
            collect_files(&path, out)?;
        } else {
            out.push(path);
        }
    }
    Ok(())
}

fn read_dir(dir: &Path) -> RenderResult<Vec<PathBuf>> {
    let entries = std::fs::read_dir(dir).map_err(|error| RenderError::Io {
        what: format!("read_dir({}): {error}", dir.display()),
    })?;
    let mut paths = Vec::new();
    for entry in entries {
        paths.push(
            entry
                .map_err(|error| RenderError::Io {
                    what: format!("read_dir entry under {}: {error}", dir.display()),
                })?
                .path(),
        );
    }
    paths.sort();
    Ok(paths)
}

fn file_name(path: &Path) -> RenderResult<String> {
    path.file_name()
        .and_then(|name| name.to_str())
        .map(str::to_string)
        .ok_or_else(|| RenderError::Io {
            what: format!("non-UTF-8 path {}", path.display()),
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write(root: &Path, relative: &str, contents: &str) {
        let path = root.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, contents).unwrap();
    }

    #[test]
    fn self_contained_closure_excludes_generated_imports_and_companions() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        write(root, "Prelude/Base.lean", "import Batteries\n");
        write(
            root,
            "Prelude/World.lean",
            "import Prelude.Base\nimport Lean\n",
        );
        write(
            root,
            "natives/Prover/Auto.lean",
            "import Prelude.World\nimport Auto\n",
        );
        write(
            root,
            "natives/Sui/Pure.lean",
            "import Prelude.World Prover.Auto\n",
        );
        write(
            root,
            "natives/Sui/UsesGenerated.lean",
            "import MoveStdlib.MoveOption\n",
        );
        write(
            root,
            "natives/Sui/Downstream.lean",
            "import Sui.UsesGenerated\n",
        );
        write(
            root,
            "natives/Sui/BalanceLemmas.lean",
            "import Prelude.World\n",
        );
        write(root, "natives/Sui/Nested/Deep.lean", "import Sui.Pure\n");

        assert_eq!(
            self_contained_bundle_modules(root).unwrap(),
            vec![
                "Prelude.Base",
                "Prelude.World",
                "Prover.Auto",
                "Sui.Nested.Deep",
                "Sui.Pure",
            ]
        );
    }

    #[test]
    fn the_real_bundle_has_a_self_contained_core() {
        let lemmas = Path::new(env!("CARGO_MANIFEST_DIR")).join("lemmas");
        let modules = self_contained_bundle_modules(&lemmas).unwrap();
        assert!(modules.contains(&"Prelude.BoundedNat".to_string()));
        assert!(modules.contains(&"Prover.MoveAuto".to_string()));
        assert!(!modules.iter().any(|module| module.ends_with("Lemmas")));
    }

    #[test]
    fn seeding_copies_only_modules_the_output_has_not_built() {
        let temp = tempfile::tempdir().unwrap();
        let seed = temp.path().join("seed");
        let output = temp.path().join("output");
        for ext in ["olean", "ilean", "trace", "olean.hash"] {
            write(
                &seed,
                &format!(".lake/build/lib/lean/Prelude/A.{ext}"),
                "seed",
            );
            write(
                &seed,
                &format!(".lake/build/lib/lean/Prelude/AB.{ext}"),
                "seed",
            );
        }
        write(&seed, ".lake/build/ir/Prelude/A.c", "seed");
        write(&output, ".lake/build/lib/lean/Prelude/AB.trace", "own");
        write(&output, ".lake/build/lib/lean/Prelude/AB.olean", "own");

        assert_eq!(seed_lake_build(&seed, &output).unwrap(), 1);
        let built = output.join(".lake/build");
        for relative in [
            "lib/lean/Prelude/A.olean",
            "lib/lean/Prelude/A.olean.hash",
            "ir/Prelude/A.c",
        ] {
            assert_eq!(
                std::fs::read_to_string(built.join(relative)).unwrap(),
                "seed"
            );
        }
        assert_eq!(
            std::fs::read_to_string(built.join("lib/lean/Prelude/AB.olean")).unwrap(),
            "own"
        );
        assert!(!built.join("lib/lean/Prelude/AB.ilean").exists());
    }

    #[test]
    fn a_missing_seed_is_an_error() {
        let temp = tempfile::tempdir().unwrap();
        assert!(seed_lake_build(&temp.path().join("absent"), temp.path()).is_err());
    }
}

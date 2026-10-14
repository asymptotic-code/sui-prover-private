// Cast-quarantine render check (unified-backend design §5.5, Phase 0.3).
//
// Client-visible surfaces (generated defs, obligation statements, lemmas)
// must mention only client struct types, `BoundedNat`, `Option`, World typed
// views, and `DfKey` (whose `KeyEntry.of` is the one sanctioned, cast-free
// coercion). Heterogeneity machinery — `Entry`, `HasCode.proof`, `▸`,
// `Universe.interp` — may appear only in the prelude (proven once) and in
// `Generated/*Interp.lean` (instances, all `rfl`).
//
// This pass scans every rendered `.lean` file OUTSIDE the sanctioned
// locations for those tokens and reports violations to stderr. Consistent
// with `validate_program`, the check is non-fatal: the rest of the run gets
// best-effort output and CI surfaces the error lines.

use std::fs;
use std::path::Path;

const FORBIDDEN_SUBSTRINGS: &[&str] = &["Universe.interp", "HasCode.proof", "\u{25B8}"];

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// True iff `line` mentions the heterogeneous universe `Entry` type: the
/// `Bag.Entry`-qualified form, or `Entry` applied to a per-project universe
/// (`Entry BagU` / `Entry TyCode`). A bare-token check would false-positive on
/// user structs that happen to be NAMED `Entry` (`Vec_map.Entry`,
/// `Priority_queue.Entry` referenced unqualified inside their own modules), so
/// the check keys on the universe application -- which is how the
/// heterogeneous Entry always renders in generated output.
fn mentions_universe_entry(line: &str) -> bool {
    if line.contains("Bag.Entry") {
        return true;
    }
    for pat in ["Entry BagU", "Entry TyCode"] {
        for (idx, _) in line.match_indices(pat) {
            let before = line[..idx].chars().next_back();
            match before {
                Some(c) if is_ident_char(c) || c == '.' => {}
                _ => return true,
            }
        }
    }
    false
}

fn check_file(path: &Path) -> Vec<String> {
    let Ok(content) = fs::read_to_string(path) else {
        return Vec::new();
    };
    let mut violations = Vec::new();
    for (lineno, line) in content.lines().enumerate() {
        let code = match line.find("--") {
            Some(i) => &line[..i],
            None => line,
        };
        for tok in FORBIDDEN_SUBSTRINGS {
            if code.contains(tok) {
                violations.push(format!(
                    "{}:{}: forbidden heterogeneity token `{}` outside the cast quarantine",
                    path.display(),
                    lineno + 1,
                    tok
                ));
            }
        }
        if mentions_universe_entry(code) {
            violations.push(format!(
                "{}:{}: universe `Entry` mentioned outside the cast quarantine",
                path.display(),
                lineno + 1
            ));
        }
    }
    violations
}

/// Scan the rendered output tree. Sanctioned locations (skipped): `Prelude/`,
/// `Generated/`, hand-written `*Natives.lean` files, user-maintained `Proofs/`
/// and `Termination/`, and lake-internal directories.
pub fn check_output_dir(output_dir: &Path) {
    let mut violations = Vec::new();
    let mut stack = vec![output_dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name().to_string_lossy().to_string();
            if path.is_dir() {
                if name.starts_with('.')
                    || matches!(
                        name.as_str(),
                        "Prelude" | "Generated" | "Proofs" | "Termination" | "lake-packages"
                    )
                {
                    continue;
                }
                stack.push(path);
            } else if name.ends_with(".lean") && !name.ends_with("Natives.lean") {
                violations.extend(check_file(&path));
            }
        }
    }
    if !violations.is_empty() {
        eprintln!(
            "Cast-quarantine check: {} violation(s) in rendered output:",
            violations.len()
        );
        for v in &violations {
            eprintln!("  error: {}", v);
        }
    }
}

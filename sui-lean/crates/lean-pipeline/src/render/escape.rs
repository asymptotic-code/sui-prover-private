//! Identifier and namespace escaping for Lean output.
//!
//! Centralizes Move-to-Lean spelling rules and collision avoidance.

/// Lean built-in type names that we prefix with `Move` to avoid collision.
const LEAN_BUILTIN_TYPES: &[&str] = &[
    "Option", "Result", "List", "Array", "String", "Vector", "Nat", "Int", "Bool", "Unit", "Char",
    "Float", "Sum", "Prod", "Sigma", "Subtype", "Quotient", "IO", "Task", "HashMap", "HashSet",
    "RBMap", "RBSet",
];

/// Lean module / namespace names we prefix with `Move`.
const LEAN_BUILTIN_MODULES: &[&str] = &[
    "vector", "option", "string", "list", "array", "nat", "int", "bool", "io", "system", "float",
];

/// Lean reserved names that cannot appear as namespace components.
const LEAN_RESERVED_NAMES: &[&str] = &["Sort", "Type", "Prop"];

/// Prefix a struct/type name with `Move` if it collides with a Lean built-in.
pub fn escape_struct_name(name: &str) -> String {
    if LEAN_BUILTIN_TYPES.contains(&name) {
        format!("Move{}", name)
    } else {
        name.to_string()
    }
}

/// Convert a Move module name to its short Lean namespace name (no
/// package prefix). Used inside lemma packages where module names
/// are globally unique across the lemma set, and as the trailing
/// segment of `module_render_namespace` for user packages.
pub fn module_name_to_namespace(module_name: &str) -> String {
    if LEAN_BUILTIN_MODULES.contains(&module_name) {
        return format!("Move{}", capitalize_first(module_name));
    }
    let cap = capitalize_first(module_name);
    if LEAN_RESERVED_NAMES.contains(&cap.as_str()) {
        format!("Move{}", cap)
    } else {
        cap
    }
}

/// Lemma packages whose hand-written natives Lean files use bare
/// (non-package-qualified) `namespace <Module>` declarations. Module
/// names are globally unique across this set, so no cross-package
/// collision risk -- and changing them to package-qualified form
/// would require rewriting every hand-written natives file.
///
/// Any package NOT in this set is a "user package" and gets its
/// translated modules emitted with a `namespace <Package>.<Module>`
/// (package-qualified) declaration. This avoids the collision
/// where two user packages each define a `module state` -- both
/// would render to `namespace State` and Lean rejects the second
/// `State.foo` import.
pub fn is_lemma_package(pkg: &str) -> bool {
    matches!(pkg, "Sui" | "MoveStdlib" | "Prover")
}

/// Compute the Lean namespace used by a translated module. For
/// lemma packages: short module name (`Bag`, `Accumulator`). For
/// user packages: package-qualified (`Pyth.State`,
/// `upshift_vaults.Admin`). Used both for the `namespace ...`
/// declaration inside the rendered file and for cross-module
/// references at use sites.
pub fn module_render_namespace(pkg: &str, module_name: &str) -> String {
    let short = module_name_to_namespace(module_name);
    if is_lemma_package(pkg) {
        short
    } else {
        format!("{}.{}", pkg, short)
    }
}

fn capitalize_first(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
    }
}

/// Escape Move identifiers that would collide with Lean keywords or use
/// characters Lean rejects in identifiers. Conservative: every collision
/// we know to map gets handled; unknown identifiers pass through.
pub fn escape_identifier(name: &str) -> String {
    // Bare `_` is Lean's anonymous binder / inference placeholder. A
    // Move parameter named `_` (allowed for "intentionally unused"
    // params) emits as `(_ : T)` in the function signature -- which
    // is valid -- but body references `_` then fail because Lean
    // tries to synthesize the placeholder. Rename to `_arg` so the
    // identifier is a real binder.
    if name == "_" {
        return "_arg".to_string();
    }
    let name = if let Some(rest) = name.strip_prefix('$') {
        format!("t_{}", rest)
    } else {
        name.replace('$', "_t_")
    };
    let name = name.replace('#', "_");
    // Move's qualifier separator `::` (e.g. `prover::asserts`) isn't
    // valid in Lean identifiers. Real-IR function names are bare
    // module-locals (`asserts` with module `prover` tracked
    // separately), but some fixtures embed the qualifier in the name.
    // Map to a Lean-safe `_` so the rendered stub at least parses.
    let name = name.replace("::", "_");

    if let Some((base, suffix)) = name.split_once('.') {
        let escaped_base = escape_identifier(base);
        if escaped_base != base {
            return format!("{}.{}", escaped_base, suffix);
        }
    }

    match name.as_str() {
        // Control flow / binding
        "if" | "then" | "else" | "let" | "in" | "do" | "for" | "while" | "match" | "fun"
        | "λ"
        // Declarations
        | "axiom" | "theorem" | "lemma" | "example" | "opaque" | "def" | "abbrev"
        | "structure" | "inductive" | "instance" | "class" | "namespace" | "section"
        | "variable" | "universe" | "import" | "open"
        // Proof / tactic
        | "by" | "from" | "using" | "have" | "show" | "suffices" | "obtain" | "this"
        | "rfl" | "decide" | "intro" | "exact" | "apply" | "refine"
        // Type / quantifier keywords
        | "forall" | "exists" | "Type" | "Prop" | "Sort"
        // Pattern / modifier keywords
        | "where" | "with" | "private" | "protected" | "noncomputable" | "mutual"
        | "partial" | "deriving" | "end"
        // Position / rewrite keywords (tactic blocks, `rw [...] at h`)
        | "at"
        // Module-initializer keyword (`initialize foo := ...`); collides with
        // the very common Move idiom of naming functions `initialize`.
        | "initialize"
        // `include`: Lean theorem-variable inclusion keyword; collides with
        // the Move parameter idiom `(include: bool)` (e.g. find_next in
        // skip_list / linked_table).
        | "include"
        // `default`: the renderer emits bare `default` for `Inhabited.default`
        // as a polymorphic placeholder (in BorrowMapKey writeback fallback
        // lambdas, struct-field stubs, etc.). A Move function literally
        // named `default` (current-lending::protocol::Referral::default)
        // shadows it inside the rendered module namespace, so every use of
        // `default` inside that module resolves to the function instead of
        // the type-class method. Escape to `default_`.
        | "default"
        // Numeric / arithmetic that Lean reserves
        | "true" | "false" => {
            format!("{}_", name)
        }
        _ => name,
    }
}

use codespan_reporting::term::termcolor::Buffer;
use dir_test::{dir_test, Fixture};
use move_compiler::editions::Flavor;
use move_compiler::shared::known_attributes::ModeAttribute;
use move_package::BuildConfig as MoveBuildConfig;
use move_prover_boogie_backend::{
    generator::run_move_prover_with_model, generator_options::Options,
};
use regex::Regex;
use std::collections::BTreeMap;
use std::fs::{copy, create_dir_all, read_to_string};
use std::path::{Path, PathBuf};
use sui_prover::build_model::move_model_for_package_legacy_unlocked;
use sui_prover::prove::DEFAULT_EXECUTION_TIMEOUT_SECONDS;

/// Runs the prover on the given file path and returns the output as a string
fn run_prover(file_path: &Path) -> String {
    let prover_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("packages")
        .join("sui-prover");
    // Convert path to use forward slashes for TOML (even on Windows)
    let prover_dir_dis = prover_dir.display().to_string().replace('\\', "/");
    let tmp = tempfile::tempdir().unwrap();
    let tmp_dir = tmp.path();
    std::fs::write(
        tmp_dir.join("Move.toml"),
        format!(
            r###"
[package]
name = "integration-test"
version = "0.0.1"
published-at = "0x2"
edition = "2024.beta"
[dependencies]
SuiProver = {{ local = "{prover_dir_dis}", override = true }}
[addresses]
integration-test = "0x9"
"###
        ),
    )
    .unwrap();
    let sources_dir = tmp_dir.join("sources");
    // create the sources_dir if it doesn't exist
    if !sources_dir.clone().exists() {
        create_dir_all(sources_dir.clone()).unwrap();
    }

    // Extract the relative path from tests/inputs/
    let relative_path = file_path
        .strip_prefix(Path::new("tests/inputs"))
        .unwrap_or_else(|_| Path::new(file_path.file_name().unwrap()));

    let extra_bpl_path = file_path
        .strip_prefix(Path::new("tests/inputs"))
        .map(|p| {
            Path::new("tests/extra_prelude")
                .join(p)
                .with_extension("bpl")
        })
        .unwrap_or(PathBuf::from("prelude_extra.bpl"));

    // Join it to the sources directory
    let new_file_path = sources_dir.join(relative_path);

    // Create parent directories if needed
    if let Some(parent_dir) = new_file_path.parent() {
        create_dir_all(parent_dir).unwrap();
    }

    // Copy the file
    copy(file_path, &new_file_path).unwrap();

    // Copy any .bpl files in the same directory (for extra_bpl attribute tests)
    // The extra_bpl path is resolved relative to the source file's directory
    if let Some(parent) = file_path.parent() {
        let full_parent = Path::new(env!("CARGO_MANIFEST_DIR")).join(parent);
        if let Ok(entries) = std::fs::read_dir(&full_parent) {
            for entry in entries.flatten() {
                let entry_path = entry.path();
                if entry_path.extension().map_or(false, |ext| ext == "bpl") {
                    let bpl_dest = new_file_path
                        .parent()
                        .unwrap()
                        .join(entry_path.file_name().unwrap());
                    copy(&entry_path, &bpl_dest).ok();
                }
            }
        }
    }

    // Tests under `pure_boogie/` snapshot the generated Boogie for the module's
    // `$pure` functions on top of the verification verdict, so a regression that
    // silently changes what a pure function *means* (rather than whether it
    // verifies) shows up in the diff.
    let is_pure_boogie_test = file_path
        .components()
        .any(|c| c.as_os_str().to_string_lossy() == "pure_boogie");

    let output_dir = Path::new(&Options::default().output_path)
        .join(relative_path.with_extension(""))
        .to_string_lossy()
        .to_string();

    // Setup cleanup that will execute even in case of panic or early return
    let result = std::panic::catch_unwind(|| {
        // Set up the build config
        let mut config = MoveBuildConfig::default();
        config.default_flavor = Some(Flavor::Sui);
        config.silence_warnings = false; // Disable warning suppression
        config.modes = vec![ModeAttribute::VERIFY_ONLY.into()];
        config.skip_fetch_latest_git_deps = true;

        // Try to build the model (using unlocked version for parallel test execution)
        let result = match move_model_for_package_legacy_unlocked(config, tmp_dir) {
            Ok(model) => {
                // Create prover options
                let mut options = Options::default();
                options.backend.sequential_task = true;
                options.backend.use_array_theory = false; // we are not using them by default
                options.backend.vc_timeout = DEFAULT_EXECUTION_TIMEOUT_SECONDS;
                options.backend.prelude_extra = Some(extra_bpl_path);
                options.backend.debug_trace = false;
                options.prover.debug_trace = false;
                options.backend.keep_artifacts = true;
                options.output_path = output_dir.clone();

                // Use a buffer to capture output instead of stderr
                let mut error_buffer = Buffer::no_color();

                tokio::runtime::Runtime::new().unwrap().block_on(async {
                    // Run the prover with the buffer to capture all output
                    let prover_result = match run_move_prover_with_model(
                        &model,
                        &mut error_buffer,
                        options.clone(),
                        None,
                    )
                    .await
                    {
                        Ok(output) => {
                            let error_output =
                                String::from_utf8_lossy(&error_buffer.into_inner()).to_string();
                            format!("{output}\n{error_output}")
                        }
                        Err(err) => {
                            // Get the captured error output as string
                            let error_output =
                                String::from_utf8_lossy(&error_buffer.into_inner()).to_string();
                            format!("{}\n{}", err, error_output)
                        }
                    };

                    prover_result
                })
            }
            Err(err) => {
                // For model-building errors, we need to reformat the error to match the expected format
                format!("We hit an error: \n{}", err)
            }
        };

        post_process_output(result, sources_dir)
    });

    // Now handle the result of our operation
    let output = match result {
        Ok(output) => output,
        Err(err) => format!(
            "Verification failed, panic during verification: {:?}",
            err.downcast_ref::<String>().unwrap_or(&String::new())
        ),
    };

    if is_pure_boogie_test {
        format!(
            "{output}\n============ generated Boogie ================\n\n{}",
            extract_test_pure_functions(&output_dir)
        )
    } else {
        output
    }
}

/// Collect the bodies of the `$pure` Boogie functions the test module itself
/// declares (test modules all live at address `0x42`, so framework `$pure`
/// helpers are filtered out by name).
///
/// A run emits one `.bpl` per spec and each carries only the pure functions that
/// spec reaches, so every file is scanned and the definitions are keyed by name:
/// the result is the union, in a stable order, regardless of directory order.
fn extract_test_pure_functions(output_dir: &str) -> String {
    let bpl_files = match std::fs::read_dir(output_dir) {
        Ok(entries) => entries
            .flatten()
            .map(|entry| entry.path())
            .filter(|path| path.extension().map_or(false, |ext| ext == "bpl"))
            .collect::<Vec<PathBuf>>(),
        Err(_) => return "<no output directory>".to_string(),
    };

    let mut by_name: BTreeMap<String, String> = BTreeMap::new();
    for path in bpl_files {
        let Ok(content) = read_to_string(&path) else {
            continue;
        };
        let mut lines = content.lines();
        while let Some(line) = lines.next() {
            if !(line.starts_with("function") && line.contains("$42_") && line.contains("$pure(")) {
                continue;
            }
            let name = line
                .split_once("$pure(")
                .map(|(head, _)| head.to_string())
                .unwrap_or_else(|| line.to_string());
            let mut definition = vec![line.to_string()];
            for body_line in lines.by_ref() {
                definition.push(body_line.to_string());
                if body_line == "}" {
                    break;
                }
            }
            by_name.insert(name, definition.join("\n"));
        }
    }

    if by_name.is_empty() {
        return "<no module $pure functions found>".to_string();
    }
    by_name.into_values().collect::<Vec<_>>().join("\n\n")
}

fn post_process_output(output: String, sources_dir: PathBuf) -> String {
    // replace numbers such as 52571u64 with ELIDEDu64 to avoid snapshot diffs
    let output = output.replace(&format!("{}", sources_dir.display()), "tests/inputs");

    // make absolute paths referencing other packages (e.g. prover) relative
    let base_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let output = output.replace(&format!("{}", base_dir.display()), "tests/../../..");

    // Normalize .move cache directory paths to avoid CI runner differences
    // Replace paths like /Users/runner/.move/... or /home/user/.move/... with a normalized path
    let re_move_cache = Regex::new(r"(?:/Users/[^/]+|/home/[^/]+)/\.move/").unwrap();
    let output = re_move_cache.replace_all(&output, "/NORMALIZED_HOME/.move/");

    // Normalize git branch names in .move cache paths (e.g., _git_more, _git_next, _git_main)
    // This handles paths like: /NORMALIZED_HOME/.move/https___github_com_asymptotic-code_sui_git_XXX/
    let re_git_branch = Regex::new(r"(https___github_com_[^/]+_sui)_git_[^/]+/").unwrap();
    let output = re_git_branch.replace_all(&output, "${1}_git_NORMALIZED/");

    // Use regex to replace numbers with more than one digit followed by u64 with ELIDEDu64
    let re = Regex::new(r"\d{2,}u64").unwrap();
    re.replace_all(&output, "ELIDEDu64").to_string()
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/tests/inputs",
    glob: "**/*.move",
)]
fn move_test(fix: Fixture<&str>) {
    let absolute_path = fix.path().parse::<PathBuf>().unwrap();
    let move_path = absolute_path
        .strip_prefix(env!("CARGO_MANIFEST_DIR"))
        .unwrap();
    let output = run_prover(move_path);
    let filename = move_path.file_name().unwrap().to_string_lossy().to_string();
    let cp = move_path
        .parent()
        .unwrap()
        .components()
        .skip(2)
        .collect::<Vec<_>>();
    let cp_str = cp
        .iter()
        .map(|comp| comp.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<String>>();
    let snapshot_path = format!("snapshots/{}", cp_str.join("/"));
    insta::with_settings!({
        prepend_module_to_snapshot => false,
        snapshot_path => snapshot_path,
    }, {
        insta::assert_snapshot!(filename, output);
    });
}

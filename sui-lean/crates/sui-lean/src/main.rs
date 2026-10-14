use std::path::PathBuf;

use clap::*;
use colored::Colorize;
use futures::FutureExt;
use move_stackless_bytecode::target_filter::TargetFilterOptions;
use prove::{execute, BuildConfig, GeneralConfig, TestConfig};
use tracing::debug;

mod audit;
mod build_model;
mod lean_pipeline_overrides;
mod lean_test;
mod legacy_builder;
mod prove;
mod system_dependencies;
mod test_results;

#[derive(Parser)]
#[clap(
    name = env!("CARGO_BIN_NAME"),
    about = "Command-line tool for formal verification of Move code within Sui projects using Lean 4. When executed from the project's root directory, it attempts to prove all specifications annotated with #[spec(prove)]",
    rename_all = "kebab-case",
    author,
    version = env!("CARGO_PKG_VERSION"),
)]
pub struct Args {
    /// Path to package directory with a Move.toml inside
    #[clap(long = "path", short = 'p', global = true)]
    pub package_path: Option<PathBuf>,

    /// Directory to write generated Lean output into. Defaults to
    /// `<package>/output` inside the target package.
    #[clap(long = "output-dir", global = true)]
    pub output_dir: Option<PathBuf>,

    /// Build the prebuilt-OLean seed for the self-contained Lean model bundle
    /// into this directory and exit. Point SUI_LEAN_OLEAN_SEED at it so every
    /// render reuses those OLeans instead of elaborating them again.
    #[clap(long = "build-olean-seed")]
    pub build_olean_seed: Option<PathBuf>,

    /// General options
    #[clap(flatten)]
    pub general_config: GeneralConfig,

    /// Package build options
    #[clap(flatten)]
    pub build_config: BuildConfig,

    /// Filtering options
    #[clap(flatten)]
    pub filter_config: TargetFilterOptions,

    /// `--test` pipeline options
    #[clap(flatten)]
    pub test_config: TestConfig,
}

#[tokio::main]
async fn main() {
    #[cfg(windows)]
    colored::control::set_virtual_terminal(true).unwrap();

    let args = Args::parse();

    let _guard = telemetry_subscribers::TelemetryConfig::new("sui-lean")
        .with_log_file("sui-lean.log")
        .with_log_level("debug")
        .with_env()
        .init();

    debug!("Sui-Lean CLI version: {}", env!("CARGO_PKG_VERSION"));

    if let Some(seed_dir) = args.build_olean_seed.as_deref() {
        if let Err(err) = prove::build_olean_seed(seed_dir) {
            eprintln!("{}", format!("{err:#}").bold().red());
            std::process::exit(1);
        }
        return;
    }

    // Wrap the entire pipeline in `catch_unwind` so panics from the
    // upstream Move-model / stackless-bytecode pipeline (e.g. `module
    // not found: ghost`, missing methods on framework types after a Sui
    // bump) surface as a structured error instead of aborting the
    // process. This matters when running across many packages: a single
    // bad package shouldn't take down the whole batch.
    let fut = execute(
        args.package_path.as_deref(),
        args.general_config,
        args.build_config,
        args.filter_config,
        args.test_config,
        args.output_dir.as_deref(),
    );
    let result = std::panic::AssertUnwindSafe(fut).catch_unwind().await;

    match result {
        Ok(Ok(_)) => (),
        Ok(Err(err)) => {
            eprintln!("{}", format!("{err:#}").bold().red());
            std::process::exit(1);
        }
        Err(panic_payload) => {
            let msg = if let Some(s) = panic_payload.downcast_ref::<&'static str>() {
                (*s).to_string()
            } else if let Some(s) = panic_payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "<non-string panic payload>".to_string()
            };
            eprintln!("{}", format!("sui-lean panicked: {msg}").bold().red());
            std::process::exit(101);
        }
    }
}

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use super::{ModId, Module, Program};

pub const ABORT_ORIGINS_FILE: &str = "abort_origins.toml";
pub const ABORT_ORIGINS_SCHEMA_VERSION: u32 = 1;
pub const UNKNOWN_ABORT_ORIGIN_TAG: u64 = 0;

#[repr(u64)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum ObservedErrorKind {
    #[default]
    Unknown = 0,
    Abort = 1,
    Arithmetic = 2,
    VectorOperation = 3,
}

impl ObservedErrorKind {
    pub const fn tag(self) -> u64 {
        self as u64
    }
}

impl TryFrom<u64> for ObservedErrorKind {
    type Error = u64;

    fn try_from(tag: u64) -> Result<Self, Self::Error> {
        match tag {
            0 => Ok(Self::Unknown),
            1 => Ok(Self::Abort),
            2 => Ok(Self::Arithmetic),
            3 => Ok(Self::VectorOperation),
            other => Err(other),
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum AbortPayloadMode {
    #[default]
    Proof,
    ObservedTest,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AbortProvenance {
    pub mode: AbortPayloadMode,
    origins: BTreeMap<u64, String>,
    module_tags: BTreeMap<ModId, u64>,
    addressed_module_tags: BTreeMap<String, u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbortProvenanceError {
    pub addressed_module: String,
    pub first_module: ModId,
    pub duplicate_module: ModId,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AbortOriginsDocument {
    pub schema_version: u32,
    pub origins: Vec<AbortOriginEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AbortOriginEntry {
    pub tag: u64,
    pub module: String,
}

impl AbortOriginsDocument {
    pub fn validate(&self) -> Result<(), String> {
        if self.schema_version != ABORT_ORIGINS_SCHEMA_VERSION {
            return Err(format!(
                "unsupported schema version {}",
                self.schema_version
            ));
        }
        let mut tags = BTreeSet::new();
        let mut modules = BTreeSet::new();
        for origin in &self.origins {
            if origin.tag == UNKNOWN_ABORT_ORIGIN_TAG {
                return Err("reserved abort origin tag 0".into());
            }
            if !tags.insert(origin.tag) {
                return Err(format!("duplicate abort origin tag {}", origin.tag));
            }
            if !modules.insert(origin.module.as_str()) {
                return Err(format!("duplicate abort origin module `{}`", origin.module));
            }
            if !is_canonical_addressed_module(&origin.module) {
                return Err(format!("non-canonical abort origin `{}`", origin.module));
            }
        }
        Ok(())
    }
}

impl AbortProvenance {
    pub fn configure(
        program: &mut Program,
        mode: AbortPayloadMode,
    ) -> Result<(), AbortProvenanceError> {
        let mut entries = BTreeMap::new();
        for (module_id, module) in &program.modules {
            let Some(addressed_module) = canonical_addressed_module(module) else {
                continue;
            };
            if let Some(first_module) = entries.insert(addressed_module.clone(), *module_id) {
                return Err(AbortProvenanceError {
                    addressed_module,
                    first_module,
                    duplicate_module: *module_id,
                });
            }
        }

        let mut origins = BTreeMap::new();
        let mut module_tags = BTreeMap::new();
        let mut addressed_module_tags = BTreeMap::new();
        if mode == AbortPayloadMode::ObservedTest {
            for (index, (module, module_id)) in entries.into_iter().enumerate() {
                let tag = u64::try_from(index + 1).expect("abort origin tag count fits in u64");
                origins.insert(tag, module.clone());
                module_tags.insert(module_id, tag);
                addressed_module_tags.insert(module, tag);
            }
        }
        program.abort_provenance = Self {
            mode,
            origins,
            module_tags,
            addressed_module_tags,
        };
        Ok(())
    }

    pub fn tag_for_module(&self, module: ModId) -> u64 {
        self.module_tags
            .get(&module)
            .copied()
            .unwrap_or(UNKNOWN_ABORT_ORIGIN_TAG)
    }

    pub fn tag_for_addressed_module(&self, module: &str) -> u64 {
        self.addressed_module_tags
            .get(module)
            .copied()
            .unwrap_or(UNKNOWN_ABORT_ORIGIN_TAG)
    }

    pub fn document(&self) -> AbortOriginsDocument {
        AbortOriginsDocument {
            schema_version: ABORT_ORIGINS_SCHEMA_VERSION,
            origins: self
                .origins
                .iter()
                .map(|(tag, module)| AbortOriginEntry {
                    tag: *tag,
                    module: module.clone(),
                })
                .collect(),
        }
    }
}

pub fn canonical_addressed_module(module: &Module) -> Option<String> {
    let address = module.address.strip_prefix("0x").unwrap_or(&module.address);
    if address.is_empty() || !address.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return None;
    }
    let canonical = address.trim_start_matches('0');
    let canonical = if canonical.is_empty() { "0" } else { canonical };
    Some(format!(
        "0x{}::{}",
        canonical.to_ascii_lowercase(),
        module.name
    ))
}

pub fn is_canonical_addressed_module(value: &str) -> bool {
    let Some((address, module)) = value.split_once("::") else {
        return false;
    };
    let Some(hex) = address.strip_prefix("0x") else {
        return false;
    };
    !module.is_empty()
        && !module.contains("::")
        && !hex.is_empty()
        && (hex.len() == 1 || !hex.starts_with('0'))
        && hex
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module(address: &str, name: &str) -> Module {
        Module {
            name: name.to_string(),
            package_name: "Pkg".to_string(),
            address: address.to_string(),
            required_imports: Vec::new(),
            is_native: false,
        }
    }

    #[test]
    fn addressed_module_is_canonical_and_parseable() {
        assert_eq!(
            canonical_addressed_module(&module(
                "0000000000000000000000000000000000000000000000000000000000000002",
                "coin"
            )),
            Some("0x2::coin".to_string())
        );
        assert_eq!(
            canonical_addressed_module(&module("0x0000", "zero")),
            Some("0x0::zero".to_string())
        );
        assert_eq!(canonical_addressed_module(&module("", "synthetic")), None);
        assert!(is_canonical_addressed_module("0x0::zero"));
        assert!(is_canonical_addressed_module("0xabc::module"));
        for invalid in ["1::m", "0x01::m", "0xA::m", "0x1::", "0x1::m::n"] {
            assert!(!is_canonical_addressed_module(invalid), "{invalid}");
        }
    }

    #[test]
    fn observed_tags_are_deterministic_and_reserve_zero() {
        let mut program = Program::default();
        program.modules.insert(7, module("2", "z"));
        program.modules.insert(3, module("1", "a"));
        program.modules.insert(4, module("", "synthetic"));

        AbortProvenance::configure(&mut program, AbortPayloadMode::ObservedTest).unwrap();

        assert_eq!(program.abort_provenance.tag_for_module(3), 1);
        assert_eq!(program.abort_provenance.tag_for_module(7), 2);
        assert_eq!(program.abort_provenance.tag_for_module(4), 0);
        assert_eq!(
            program.abort_provenance.document(),
            AbortOriginsDocument {
                schema_version: 1,
                origins: vec![
                    AbortOriginEntry {
                        tag: 1,
                        module: "0x1::a".to_string(),
                    },
                    AbortOriginEntry {
                        tag: 2,
                        module: "0x2::z".to_string(),
                    },
                ],
            }
        );
    }

    #[test]
    fn sidecar_is_toml_and_proof_mode_removes_it() {
        let output = tempfile::tempdir().unwrap();
        let mut program = Program::default();
        program.modules.insert(0, module("2", "coin"));
        AbortProvenance::configure(&mut program, AbortPayloadMode::ObservedTest).unwrap();

        crate::render::write_abort_origins_sidecar(&program, output.path()).unwrap();
        let path = output.path().join(ABORT_ORIGINS_FILE);
        assert_eq!(
            std::fs::read_to_string(&path).unwrap(),
            "schema_version = 1\n\n[[origins]]\ntag = 1\nmodule = \"0x2::coin\"\n"
        );
        assert_eq!(
            crate::render::read_abort_origins_sidecar(output.path()).unwrap(),
            program.abort_provenance.document()
        );

        AbortProvenance::configure(&mut program, AbortPayloadMode::Proof).unwrap();
        crate::render::write_abort_origins_sidecar(&program, output.path()).unwrap();
        assert!(!path.exists());
    }

    #[test]
    fn duplicate_addressed_modules_are_rejected() {
        let mut program = Program::default();
        program.modules.insert(7, module("2", "coin"));
        program.modules.insert(3, module("0x0002", "coin"));

        let error =
            AbortProvenance::configure(&mut program, AbortPayloadMode::ObservedTest).unwrap_err();
        assert_eq!(error.addressed_module, "0x2::coin");
        assert_eq!(error.first_module, 3);
        assert_eq!(error.duplicate_module, 7);
    }

    #[test]
    fn sidecar_reader_rejects_unknown_fields_and_duplicate_identities() {
        let output = tempfile::tempdir().unwrap();
        let path = output.path().join(ABORT_ORIGINS_FILE);
        std::fs::write(
            &path,
            "schema_version = 1\nunknown = true\n\n[[origins]]\ntag = 1\nmodule = \"0x1::m\"\n",
        )
        .unwrap();
        assert!(crate::render::read_abort_origins_sidecar(output.path()).is_err());

        std::fs::write(
            &path,
            "schema_version = 1\n\n[[origins]]\ntag = 1\nmodule = \"0x1::m\"\n\n[[origins]]\ntag = 1\nmodule = \"0x2::n\"\n",
        )
        .unwrap();
        assert!(crate::render::read_abort_origins_sidecar(output.path()).is_err());

        std::fs::write(
            &path,
            "schema_version = 1\n\n[[origins]]\ntag = 1\nmodule = \"0x1::m\"\n\n[[origins]]\ntag = 2\nmodule = \"0x1::m\"\n",
        )
        .unwrap();
        assert!(crate::render::read_abort_origins_sidecar(output.path()).is_err());
    }
}

use anyhow::{Context, Result};
use serde::Serialize;
use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Mutex;

pub const SCHEMA_VERSION: u32 = 1;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    Pass,
    Fail,
    Unsupported,
    Timeout,
    Infra,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct TestRecord {
    pub name: String,
    pub status: Status,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason_code: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
}

#[derive(Debug, Default)]
pub struct Recorder {
    records: Mutex<BTreeMap<String, TestRecord>>,
}

impl Recorder {
    pub fn record(&self, record: TestRecord) {
        let mut records = self.records.lock().expect("test result mutex poisoned");
        match records.get(&record.name) {
            Some(existing) if priority(existing.status) >= priority(record.status) => {}
            _ => {
                records.insert(record.name.clone(), record);
            }
        }
    }

    pub fn records(&self) -> Vec<TestRecord> {
        self.records
            .lock()
            .expect("test result mutex poisoned")
            .values()
            .cloned()
            .collect()
    }
}

fn priority(status: Status) -> u8 {
    match status {
        Status::Pass => 0,
        Status::Fail => 1,
        Status::Unsupported => 2,
        Status::Timeout => 3,
        Status::Infra => 4,
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize)]
pub struct Totals {
    pub selected: usize,
    #[serde(rename = "pass")]
    pub passed: usize,
    pub fail: usize,
    pub unsupported: usize,
    pub timeout: usize,
    pub infra: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct Document {
    pub schema_version: u32,
    pub phase: String,
    pub totals: Totals,
    #[serde(rename = "tests")]
    pub records: Vec<TestRecord>,
}

impl Document {
    pub fn new(phase: impl Into<String>, mut records: Vec<TestRecord>) -> Self {
        records.sort_by(|a, b| a.name.cmp(&b.name));
        let mut totals = Totals {
            selected: records.len(),
            ..Totals::default()
        };
        for record in &records {
            match record.status {
                Status::Pass => totals.passed += 1,
                Status::Fail => totals.fail += 1,
                Status::Unsupported => totals.unsupported += 1,
                Status::Timeout => totals.timeout += 1,
                Status::Infra => totals.infra += 1,
            }
        }
        Self {
            schema_version: SCHEMA_VERSION,
            phase: phase.into(),
            totals,
            records,
        }
    }

    pub fn write_atomic(&self, path: &Path) -> Result<()> {
        if let Some(parent) = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
        {
            std::fs::create_dir_all(parent)
                .with_context(|| format!("creating {}", parent.display()))?;
        }
        let encoded = toml::to_string_pretty(self).context("serializing test results TOML")?;
        let file_name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("test_results.toml");
        let temporary = path.with_file_name(format!(".{file_name}.{}.tmp", std::process::id()));
        std::fs::write(&temporary, encoded)
            .with_context(|| format!("writing {}", temporary.display()))?;
        std::fs::rename(&temporary, path)
            .with_context(|| format!("renaming {} to {}", temporary.display(), path.display()))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn serializes_stable_schema_and_totals() {
        let document = Document::new(
            "run",
            vec![
                TestRecord {
                    name: "0x1::m::b".into(),
                    status: Status::Unsupported,
                    reason_code: Some("abort_origin_missing".into()),
                    detail: Some("origin unavailable".into()),
                },
                TestRecord {
                    name: "0x1::m::a".into(),
                    status: Status::Pass,
                    reason_code: None,
                    detail: None,
                },
            ],
        );
        let encoded = toml::to_string_pretty(&document).unwrap();
        assert!(encoded.contains("schema_version = 1"));
        assert!(encoded.contains("phase = \"run\""));
        assert!(encoded.contains("selected = 2"));
        assert!(encoded.contains("pass = 1"));
        assert!(encoded.contains("unsupported = 1"));
        assert!(encoded.contains("status = \"pass\""));
        assert_eq!(document.records[0].name, "0x1::m::a");
    }

    #[test]
    fn recorder_keeps_the_most_severe_iteration() {
        let recorder = Recorder::default();
        for status in [
            Status::Pass,
            Status::Unsupported,
            Status::Fail,
            Status::Infra,
        ] {
            recorder.record(TestRecord {
                name: "0x1::m::test".into(),
                status,
                reason_code: None,
                detail: None,
            });
        }
        let records = recorder.records();
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].status, Status::Infra);
    }

    #[test]
    fn unsupported_iteration_is_not_hidden_by_an_ordinary_failure() {
        let recorder = Recorder::default();
        for status in [Status::Fail, Status::Unsupported] {
            recorder.record(TestRecord {
                name: "0x1::m::test".into(),
                status,
                reason_code: None,
                detail: None,
            });
        }
        assert_eq!(recorder.records()[0].status, Status::Unsupported);
    }
}

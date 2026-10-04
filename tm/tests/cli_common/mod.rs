//! Shared harness for the `tm` CLI integration tests (tm-spec-v1.md §17 M5:
//! "every verb in §13 has an integration test against a temp `plan/` dir").
//!
//! [`Tm::new`] copies `tm-core/tests/fixtures/plan-basic` into a fresh
//! [`tempfile::TempDir`] (the fixture itself is never touched) and runs the
//! built binary against it with a fixed `--now`, so every run is
//! deterministic — the same instant, the same ids, the same plan hash.

#![allow(dead_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;
use tempfile::TempDir;

/// The instant most tests run at: Monday 2026-09-07 09:00 in America/Chicago.
pub const NOW: &str = "2026-09-07T09:00:00-05:00";

/// **FNV-1a-64, as hex** — the digest the replay cache's manifest records for each sealed month
/// file (`kernel_log::month_digest`, the owner's D93), computed in the test harness and never
/// borrowed from the binary, so a test's reading of the rule is independent of the code under test.
/// One copy for every test binary (README gap 4504, the W-43 repair: three files carried it).
pub fn fnv1a64_hex(bytes: &[u8]) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("{h:016x}")
}

/// **`ckpt.json` with its own digest recomputed** (the campaign's D98, README gap 4394): the text after
/// the digest field — from the byte after `{"digest":"<16 hex>",` through the last newline — digested by
/// [`fnv1a64_hex`] and put back in front, as the binary writes it. What a test that edits a checkpoint
/// into one a kernel could have WRITTEN must write after its edit, so the rule it means to bite (a month
/// file's digest, a kernel id) is what refuses it and not the checkpoint's own digest. Computed here,
/// never borrowed from the binary.
pub fn ckpt_redigested(text: &str) -> String {
    let head = "{\"digest\":\"";
    let body = text
        .strip_prefix(head)
        .and_then(|rest| rest.get(16..))
        .and_then(|rest| rest.strip_prefix("\","))
        .unwrap_or_else(|| panic!("a checkpoint that opens with its digest: {}", &text[..text.len().min(80)]));
    format!("{head}{}\",{body}", fnv1a64_hex(body.as_bytes()))
}

/// One temporary plan directory and the binary under test.
pub struct Tm {
    /// The temporary root (kept alive for the test's lifetime).
    pub tmp: TempDir,
    /// The plan directory inside it.
    pub plan: PathBuf,
}

/// What one run produced.
pub struct Out {
    /// The process exit code (§13).
    pub code: i32,
    /// Standard output.
    pub stdout: String,
    /// Standard error.
    pub stderr: String,
}

impl Out {
    /// The stdout parsed as JSON (`--json` runs).
    pub fn json(&self) -> Value {
        serde_json::from_str(&self.stdout)
            .unwrap_or_else(|e| panic!("stdout is not JSON ({e}): {:?}", self.stdout))
    }
}

/// Copy a directory tree.
fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("create dir");
    for entry in fs::read_dir(from).expect("read fixture") {
        let entry = entry.expect("dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).expect("copy file");
        }
    }
}

impl Tm {
    /// A temp copy of the `plan-basic` fixture.
    pub fn new() -> Tm {
        let tmp = TempDir::new().expect("temp dir");
        let plan = tmp.path().join("plan");
        let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../tm-core/tests/fixtures/plan-basic");
        copy_dir(&fixture, &plan);
        Tm { tmp, plan }
    }

    /// An empty temp directory (for `tm init`).
    pub fn empty() -> Tm {
        let tmp = TempDir::new().expect("temp dir");
        let plan = tmp.path().join("plan");
        Tm { tmp, plan }
    }

    /// Run the binary with an explicit instant.
    pub fn run_at(&self, now: &str, args: &[&str]) -> Out {
        self.run_env_at(now, &[], args)
    }

    /// Run with extra environment variables (the panic probe's hook).
    pub fn run_env_at(&self, now: &str, envs: &[(&str, &str)], args: &[&str]) -> Out {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_tm"));
        cmd.arg("--dir")
            .arg(&self.plan)
            .arg("--now")
            .arg(now)
            .args(args);
        for (k, v) in envs {
            cmd.env(k, v);
        }
        let out = cmd.output().expect("run tm");
        Out {
            code: out.status.code().unwrap_or(-1),
            stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        }
    }

    /// Run at [`NOW`] with extra environment variables.
    pub fn run_env(&self, envs: &[(&str, &str)], args: &[&str]) -> Out {
        self.run_env_at(NOW, envs, args)
    }

    /// Run at [`NOW`].
    pub fn run(&self, args: &[&str]) -> Out {
        self.run_at(NOW, args)
    }

    /// Run and assert exit code 0.
    pub fn ok_at(&self, now: &str, args: &[&str]) -> Out {
        let out = self.run_at(now, args);
        assert_eq!(
            out.code, 0,
            "`tm {}` failed: {}{}",
            args.join(" "),
            out.stdout,
            out.stderr
        );
        out
    }

    /// Run at [`NOW`] and assert exit code 0.
    pub fn ok(&self, args: &[&str]) -> Out {
        self.ok_at(NOW, args)
    }

    /// Run with `--json` at `now`, assert success, return the document.
    pub fn json_at(&self, now: &str, args: &[&str]) -> Value {
        let mut all = vec!["--json"];
        all.extend_from_slice(args);
        self.ok_at(now, &all).json()
    }

    /// Run with `--json` at [`NOW`].
    pub fn json(&self, args: &[&str]) -> Value {
        self.json_at(NOW, args)
    }

    /// The text of a file in the plan directory.
    pub fn read(&self, rel: &str) -> String {
        fs::read_to_string(self.plan.join(rel))
            .unwrap_or_else(|e| panic!("read {rel}: {e}"))
    }

    /// Whether a file exists.
    pub fn exists(&self, rel: &str) -> bool {
        self.plan.join(rel).exists()
    }

    /// The line carrying `^id`, trimmed.
    pub fn line(&self, rel: &str, id: &str) -> String {
        let needle = format!("^{id}");
        self.read(rel)
            .lines()
            .find(|l| l.split_whitespace().any(|w| w == needle))
            .unwrap_or_else(|| panic!("no line ^{id} in {rel}"))
            .trim()
            .to_string()
    }

    /// Every entry of `.tm/log.jsonl`.
    pub fn log(&self) -> Vec<Value> {
        let path = self.plan.join(".tm/log.jsonl");
        let text = fs::read_to_string(path).unwrap_or_default();
        text.lines()
            .filter(|l| !l.trim().is_empty())
            .map(|l| serde_json::from_str(l).expect("log line is JSON"))
            .collect()
    }

    /// The `ev` names in the log, in order.
    pub fn events(&self) -> Vec<String> {
        self.log()
            .iter()
            .map(|e| e["ev"].as_str().unwrap_or_default().to_string())
            .collect()
    }

    /// The last log entry.
    pub fn last(&self) -> Value {
        self.log().pop().expect("a log entry")
    }

    /// The last log entry with the given `ev`. Use this instead of [`last`]
    /// when the command under test may be followed by a replan: a non-zero
    /// energy delta re-plans the day (§8.5), so `plan` lands after `energy`.
    pub fn last_ev(&self, ev: &str) -> Value {
        self.log()
            .into_iter()
            .rfind(|e| e["ev"] == ev)
            .unwrap_or_else(|| panic!("a `{ev}` log entry"))
    }

    /// `.tm/state.json`.
    pub fn state(&self) -> Value {
        let text = fs::read_to_string(self.plan.join(".tm/state.json")).unwrap_or_default();
        serde_json::from_str(&text).unwrap_or(Value::Null)
    }
}

/// The *shape* of a JSON document: every scalar replaced by its type name,
/// every array by the shape of its first element. Snapshotting this pins the
/// `--json` schema (§17 M5) without pinning values that the planner
/// milestone will legitimately change.
pub fn schema(v: &Value) -> Value {
    match v {
        Value::Object(map) => Value::Object(
            map.iter()
                .map(|(k, val)| (k.clone(), schema(val)))
                .collect(),
        ),
        Value::Array(items) => match items.first() {
            Some(first) => Value::Array(vec![schema(first)]),
            None => Value::Array(vec![]),
        },
        Value::String(_) => Value::String("string".into()),
        Value::Bool(_) => Value::String("bool".into()),
        Value::Number(n) if n.is_f64() => Value::String("number".into()),
        Value::Number(_) => Value::String("integer".into()),
        Value::Null => Value::String("null".into()),
    }
}

/// Replace every value at `key` (at any depth) with `with` — the stand-in for
/// insta's redactions, which this workspace's `insta` features do not include.
pub fn scrub(v: &mut Value, key: &str, with: &str) {
    match v {
        Value::Object(map) => {
            for (k, val) in map.iter_mut() {
                if k == key {
                    *val = Value::String(with.to_string());
                } else {
                    scrub(val, key, with);
                }
            }
        }
        Value::Array(items) => {
            for item in items {
                scrub(item, key, with);
            }
        }
        _ => {}
    }
}

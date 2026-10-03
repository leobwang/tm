//! **A sealed month file carries a digest, and one that does not match it is rebuilt, never
//! served** — the owner's **D93** (README gap 4246, W-43 track H), driven through the binary.
//!
//! D13 lets the kernel read a sealed day record back for an explicitly old date, and until D93 the
//! cache trusted a month file as written under a valid kernel id: one byte of a record changed by
//! hand, or by a disk, was the answer `tm review day --date` gave until the next genesis — the
//! silent-wrong-answer class. `ckpt.json` now records, beside each month file the manifest names,
//! its FNV-1a-64 (`kernel_log::month_digest`, the hash §9.8's prefix digest already is), and a file
//! whose bytes do not match is never served: the cache is rebuilt from the log, as for a month file
//! that is missing (README gap 3711).
//!
//! **The bite is shown first**: the same one-byte edit WITH its digest kept consistent is served —
//! so it is the digest, and nothing else, that refuses it.

mod cli_common;

use std::fs;
use std::path::{Path, PathBuf};

use cli_common::{fnv1a64_hex, Tm};
use serde_json::Value;

/// Three days after `energy-14d.jsonl`'s last line, so the log's August days are sealed.
const LATER: &str = "2026-09-10T09:00:00-05:00";
/// The log's first day, sealed at [`LATER`]: four blocks done, 260 block minutes.
const SEALED_DATE: &str = "2026-08-25";
/// [`SEALED_DATE`] as the kernel's day number, the key its month file holds it under.
const SEALED_DAY: &str = "739852";
/// `blocksDone` in a sealed day record: the second element (the day's `Replay.DayAcc`), fourth field.
const ACC_AT: usize = 1;
const BLOCKS_DONE_AT: usize = 3;

fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/corpus")
}

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

/// `plan-basic` carrying the corpus's `energy-14d.jsonl` as its `.tm/log.jsonl`, the cache warmed.
fn warmed() -> Tm {
    let tmp = tempfile::TempDir::new().expect("temp dir");
    let plan = tmp.path().join("plan");
    copy_dir(&corpus().join("plan-basic"), &plan);
    fs::create_dir_all(plan.join(".tm")).expect("mkdir .tm");
    fs::copy(corpus().join("logs/energy-14d.jsonl"), plan.join(".tm/log.jsonl")).expect("copy the log");
    let tm = Tm { tmp, plan };
    tm.ok_at(LATER, &["now"]);
    tm
}

/// The same tree with no replay cache at all: the comparand a rebuilt answer must equal.
fn cacheless(tm: &Tm) -> Tm {
    let tmp = tempfile::TempDir::new().expect("temp dir");
    let plan = tmp.path().join("plan");
    copy_dir(&tm.plan, &plan);
    fs::remove_dir_all(plan.join(".tm/cache")).expect("delete the comparand's cache");
    Tm { tmp, plan }
}

fn cache_dir(tm: &Tm) -> PathBuf {
    tm.plan.join(".tm/cache/replay")
}

/// `ckpt.json`'s head — every key but the verbatim checkpoint.
fn ckpt(tm: &Tm) -> Value {
    let text = fs::read_to_string(cache_dir(tm).join("ckpt.json")).expect("ckpt.json");
    let at = text.find(",\"ckpt\":").expect("a checkpoint");
    serde_json::from_str(&format!("{}}}", &text[..at])).expect("the head is JSON")
}

/// The month file the manifest names for August 2026.
fn august_file(tm: &Tm) -> PathBuf {
    let head = ckpt(tm);
    cache_dir(tm).join(head["manifest"]["2026-08"].as_str().unwrap_or_else(|| panic!("no August file: {head}")))
}

/// The sealed record's `blocksDone`, read from a month file.
fn sealed_blocks_done(path: &Path) -> u64 {
    let month: Value = serde_json::from_str(&fs::read_to_string(path).expect("a month file")).expect("JSON");
    let record = &month["days"][SEALED_DAY];
    assert_eq!(record[0].as_u64(), Some(SEALED_DAY.parse().expect("a day")), "the codec moved: {record}");
    record[ACC_AT][BLOCKS_DONE_AT].as_u64().unwrap_or_else(|| panic!("no blocksDone: {record}"))
}

/// **One byte**: the record's `blocksDone` digit `4` made `3` in place. The file still reads as JSON
/// and still holds every record — it is the edit a disk or a hand makes, not a deletion.
fn edit_one_byte(path: &Path) -> String {
    let before = fs::read_to_string(path).expect("the month file");
    let at = before.find(&format!("\"{SEALED_DAY}\":[{SEALED_DAY},")).expect("the sealed record");
    let tail = &before[at..];
    let field = tail.find("],260,4,").expect("the record's block minutes and blocks done") + "],260,".len();
    let mut after = before.clone();
    after.replace_range(at + field..at + field + 1, "3");
    assert_eq!(before.len(), after.len());
    assert_eq!(before.bytes().zip(after.bytes()).filter(|(a, b)| a != b).count(), 1, "one byte");
    fs::write(path, &after).expect("write the month file");
    assert_eq!(sealed_blocks_done(path), 3, "the edit is the record's blocksDone");
    after
}

/// What `tm review day --date` answers for the sealed day, whole.
fn reviewed(tm: &Tm) -> Value {
    tm.json_at(LATER, &["review", "day", "--date", SEALED_DATE])
}

#[test]
fn every_month_file_the_manifest_names_carries_its_digest() {
    let tm = warmed();
    let head = ckpt(&tm);
    assert_eq!(head["format"], 4, "{head}");
    let manifest = head["manifest"].as_object().expect("a manifest");
    let digests = head["digests"].as_object().expect("digests");
    assert!(!manifest.is_empty(), "the fortnight seals a month");
    assert_eq!(manifest.keys().collect::<Vec<_>>(), digests.keys().collect::<Vec<_>>(), "one digest per month file");
    for (month, rel) in manifest {
        let bytes = fs::read(cache_dir(&tm).join(rel.as_str().expect("a file name"))).expect("the month file");
        assert_eq!(digests[month], fnv1a64_hex(&bytes), "{month}: the digest is the file's FNV-1a-64");
    }
}

/// **The bite**: the one-byte edit with the manifest's digest kept consistent — a file a kernel
/// could have written — IS served. Without it, the test below could pass because the record is
/// never read at all.
#[test]
fn a_one_byte_edit_whose_digest_is_kept_is_served() {
    let tm = warmed();
    assert_eq!(reviewed(&tm)["review"]["blocks_done"], 4);
    let august = august_file(&tm);
    let before = fs::read(&august).expect("the August file");
    let after = edit_one_byte(&august);
    let path = cache_dir(&tm).join("ckpt.json");
    let text = fs::read_to_string(&path).expect("ckpt.json");
    let (old, new) = (fnv1a64_hex(&before), fnv1a64_hex(after.as_bytes()));
    assert_eq!(text.matches(&format!("\"{old}\"")).count(), 1, "{text}");
    fs::write(&path, text.replace(&format!("\"{old}\""), &format!("\"{new}\""))).expect("write ckpt.json");
    assert_eq!(reviewed(&tm)["review"]["blocks_done"], 3, "a consistent month file is trusted (D13)");
}

/// **D93**: the same one-byte edit, the digest left as written, is NOT served — the answer is a
/// cache-less run's, whole; the run says once that it rebuilt; the rebuilt files match their digests
/// and the edited one is named by no manifest; the run after is silent.
#[test]
fn a_month_file_one_byte_corrupted_is_rebuilt_and_answers_as_a_cache_less_run() {
    let tm = warmed();
    let truth = reviewed(&tm);
    assert_eq!(truth["review"]["blocks_done"], 4);
    assert_eq!(reviewed(&cacheless(&tm)), truth, "the comparand: a run with no cache answers the same");
    let first_gen = ckpt(&tm)["gen"].clone();
    let august = august_file(&tm);
    let edited = edit_one_byte(&august);

    let out = tm.run_at(LATER, &["--json", "review", "day", "--date", SEALED_DATE]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("does not match its digest") && out.stderr.contains("rebuilt from the log"), "{}", out.stderr);
    assert_eq!(out.json(), truth, "a corrupted record was served");

    let head = ckpt(&tm);
    assert_ne!(head["gen"], first_gen, "no new generation was written");
    let rebuilt = august_file(&tm);
    assert_ne!(rebuilt, august, "the manifest still names the edited file");
    assert_eq!(sealed_blocks_done(&rebuilt), 4);
    for (month, rel) in head["manifest"].as_object().expect("a manifest") {
        let text = fs::read_to_string(cache_dir(&tm).join(rel.as_str().expect("a name"))).expect("a month file");
        assert_eq!(head["digests"][month], fnv1a64_hex(text.as_bytes()), "{month}");
        assert_ne!(text, edited, "{month}: the edited file is named again");
    }
    let again = tm.run_at(LATER, &["--json", "review", "day", "--date", SEALED_DATE]);
    assert_eq!((again.code, again.stderr.as_str()), (0, ""), "the healed cache says nothing");
    assert_eq!(again.json(), truth);
}

/// **A cache written before D93 is rebuilt once** — a format-3 `ckpt.json` with no digests, as the
/// binary before this change wrote it: the next verb answers as before and writes format 4; the
/// verb after it resumes that generation.
#[test]
fn a_cache_written_before_d93_is_rebuilt_once() {
    let tm = warmed();
    let truth = reviewed(&tm);
    let path = cache_dir(&tm).join("ckpt.json");
    let text = fs::read_to_string(&path).expect("ckpt.json");
    let digests = format!("\"digests\":{},", serde_json::to_string(&ckpt(&tm)["digests"]).expect("a map"));
    assert_eq!(text.matches(&digests).count(), 1, "{text}");
    fs::write(&path, text.replace(&digests, "").replace("\"format\":4", "\"format\":3")).expect("a format-3 checkpoint");
    let old_gen = ckpt(&tm)["gen"].clone();
    assert_eq!(reviewed(&tm), truth, "the answer across the rebuild");
    let head = ckpt(&tm);
    assert_eq!(head["format"], 4);
    assert_ne!(head["gen"], old_gen, "the format-3 checkpoint was resumed");
    assert_eq!(head["digests"].as_object().map(|d| d.len()), head["manifest"].as_object().map(|m| m.len()));
    assert_eq!(reviewed(&tm), truth);
    assert_eq!(ckpt(&tm)["gen"], head["gen"], "rebuilt once, not on every verb");
}

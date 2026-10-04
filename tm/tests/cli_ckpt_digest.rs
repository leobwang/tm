//! **`ckpt.json` carries a digest of its own text, and a checkpoint whose digest does not match is
//! rebuilt, never served** — the campaign's **D98** (a) (README gap 4394, W-44 track H), D93's rule
//! for a sealed month file applied to the checkpoint that names them, driven through the binary.
//!
//! Until D98 a hand edit or a disk fault inside `ckpt.json` that still read as JSON was resumed
//! from (D13 trusts the cache as written): one changed digit of a month file's recorded digest, of
//! the ledger day, of the checkpoint itself, answered until the next genesis. The checkpoint now
//! opens `{"digest":"<FNV-1a-64>",` over the rest of its own text (`kernel_log::month_digest`, the
//! hash every other file of the cache is checked by), and a text that does not match is not read:
//! the cache is rebuilt from the log and the rebuild says so once.
//!
//! **The bite is shown first**: a poisoned month file whose manifest digest AND checkpoint digest
//! are both kept consistent — a cache a kernel could have WRITTEN — is served; the same poison with
//! only the checkpoint's own digest left as it was is not. So it is the checkpoint's digest, and
//! nothing else, that refuses it.

mod cli_common;

use std::fs;
use std::path::{Path, PathBuf};

use cli_common::{ckpt_redigested, fnv1a64_hex, Tm};
use serde_json::Value;

/// Three days after `energy-14d.jsonl`'s last line, so the log's August days are sealed.
const LATER: &str = "2026-09-10T09:00:00-05:00";
/// The log's first day, sealed at [`LATER`]: four blocks done.
const SEALED_DATE: &str = "2026-08-25";
/// [`SEALED_DATE`] as the kernel's day number, the key its month file holds it under.
const SEALED_DAY: &str = "739852";

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

fn ckpt_path(tm: &Tm) -> PathBuf {
    tm.plan.join(".tm/cache/replay/ckpt.json")
}

/// `ckpt.json`'s head — every key but the verbatim checkpoint.
fn head(tm: &Tm) -> Value {
    let text = fs::read_to_string(ckpt_path(tm)).expect("ckpt.json");
    let at = text.find(",\"ckpt\":").expect("a checkpoint");
    serde_json::from_str(&format!("{}}}", &text[..at])).expect("the head is JSON")
}

/// What `tm review day --date` answers for the sealed day, whole.
fn reviewed(tm: &Tm) -> Value {
    tm.json_at(LATER, &["review", "day", "--date", SEALED_DATE])
}

/// The August month file, its sealed day's `blocksDone` digit `4` made `3`, and the manifest's
/// digest of it recomputed in the checkpoint's text: the poisoned checkpoint text, its own digest
/// left as it was.
fn poisoned_august(tm: &Tm) -> String {
    let h = head(tm);
    let august = tm.plan.join(".tm/cache/replay").join(h["manifest"]["2026-08"].as_str().expect("an August file"));
    let before = fs::read_to_string(&august).expect("the August file");
    let at = before.find(&format!("\"{SEALED_DAY}\":[{SEALED_DAY},")).expect("the sealed record");
    let field = before[at..].find("],260,4,").expect("blocks done") + "],260,".len();
    let mut after = before.clone();
    after.replace_range(at + field..at + field + 1, "3");
    fs::write(&august, &after).expect("write the August file");
    let text = fs::read_to_string(ckpt_path(tm)).expect("ckpt.json");
    let (old, new) = (fnv1a64_hex(before.as_bytes()), fnv1a64_hex(after.as_bytes()));
    assert_eq!(text.matches(&format!("\"{old}\"")).count(), 1, "{text}");
    text.replace(&format!("\"{old}\""), &format!("\"{new}\""))
}

#[test]
fn the_checkpoint_opens_with_the_digest_of_the_rest_of_its_text() {
    let tm = warmed();
    let text = fs::read_to_string(ckpt_path(&tm)).expect("ckpt.json");
    let rest = text.strip_prefix("{\"digest\":\"").expect("the digest first");
    let (hex, body) = rest.split_at(16);
    let body = body.strip_prefix("\",").expect("then the rest of the text");
    assert_eq!(hex, fnv1a64_hex(body.as_bytes()), "the digest is FNV-1a-64 of the rest");
    assert_eq!(head(&tm)["format"], 5);
    assert_eq!(ckpt_redigested(&text), text, "the harness's digest is the binary's");
}

/// **The bite**: the poison with BOTH digests kept consistent is served; with the checkpoint's own
/// digest left as written, it is not — the answer is a cache-less run's.
#[test]
fn only_the_checkpoints_own_digest_stands_between_a_poisoned_month_and_the_answer() {
    let tm = warmed();
    let truth = reviewed(&tm);
    assert_eq!(truth["review"]["blocks_done"], 4);
    let poisoned = poisoned_august(&tm);
    fs::write(ckpt_path(&tm), ckpt_redigested(&poisoned)).expect("a consistent checkpoint");
    assert_eq!(reviewed(&tm)["review"]["blocks_done"], 3, "a cache a kernel could have written is trusted (D13)");

    let tm = warmed();
    let poisoned = poisoned_august(&tm);
    fs::write(ckpt_path(&tm), &poisoned).expect("the checkpoint with its digest as it was");
    let out = tm.run_at(LATER, &["--json", "review", "day", "--date", SEALED_DATE]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(out.json(), truth, "a checkpoint that does not match its digest was resumed");
    assert_eq!(
        out.stderr.matches("ckpt.json does not match its digest; rebuilt from the log").count(),
        1,
        "{}",
        out.stderr
    );
}

/// **One byte of `ckpt.json` changed — a digit of its ledger day — is rebuilt and answers as a
/// cache-less run**: said once, a new generation whose text matches its digest, and the run after
/// it silent and resuming that generation.
#[test]
fn a_checkpoint_one_byte_corrupted_is_rebuilt_and_answers_as_a_cache_less_run() {
    let tm = warmed();
    let truth = reviewed(&tm);
    assert_eq!(reviewed(&cacheless(&tm)), truth, "the comparand: a run with no cache answers the same");
    let first_gen = head(&tm)["gen"].clone();
    let text = fs::read_to_string(ckpt_path(&tm)).expect("ckpt.json");
    let at = text.find("\"ledgerDay\":").expect("a ledger day") + "\"ledgerDay\":".len() + 5;
    let mut bytes = text.clone().into_bytes();
    bytes[at] = if bytes[at] == b'0' { b'1' } else { bytes[at] - 1 };
    let edited = String::from_utf8(bytes).expect("ASCII");
    assert_eq!(text.bytes().zip(edited.bytes()).filter(|(a, b)| a != b).count(), 1, "one byte");
    fs::write(ckpt_path(&tm), &edited).expect("the edited checkpoint");
    serde_json::from_str::<Value>(&edited).expect("the edit still reads as JSON");

    let out = tm.run_at(LATER, &["--json", "review", "day", "--date", SEALED_DATE]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(out.json(), truth, "a corrupted checkpoint was resumed");
    assert!(out.stderr.contains("ckpt.json does not match its digest; rebuilt from the log"), "{}", out.stderr);
    let healed = fs::read_to_string(ckpt_path(&tm)).expect("ckpt.json");
    assert_eq!(ckpt_redigested(&healed), healed, "the rebuilt checkpoint matches its digest");
    let gen = head(&tm)["gen"].clone();
    assert_ne!(gen, first_gen, "no new generation was written");
    let again = tm.run_at(LATER, &["--json", "review", "day", "--date", SEALED_DATE]);
    assert_eq!((again.code, again.stderr.as_str()), (0, ""), "the healed cache says nothing");
    assert_eq!(again.json(), truth);
    assert_eq!(head(&tm)["gen"], gen, "rebuilt once, not on every verb");
}

/// **A checkpoint written before D98 is rebuilt once, and not named** — format 4, no digest of its
/// own, as the binary before this change wrote it: the next verb answers as before, says nothing,
/// and writes format 5; the verb after it resumes that generation.
#[test]
fn a_checkpoint_written_before_d98_is_rebuilt_once() {
    let tm = warmed();
    let truth = reviewed(&tm);
    let text = fs::read_to_string(ckpt_path(&tm)).expect("ckpt.json");
    let body = text.strip_prefix("{\"digest\":\"").and_then(|r| r.get(16..)).and_then(|r| r.strip_prefix("\",")).expect("a body");
    let old = format!("{{{body}").replace("\"format\":5", "\"format\":4");
    fs::write(ckpt_path(&tm), &old).expect("a format-4 checkpoint");
    let old_gen = head(&tm)["gen"].clone();
    let out = tm.run_at(LATER, &["--json", "review", "day", "--date", SEALED_DATE]);
    assert_eq!((out.code, out.stderr.as_str()), (0, ""), "an older format is rebuilt and not named");
    assert_eq!(out.json(), truth);
    let h = head(&tm);
    assert_eq!(h["format"], 5);
    assert_ne!(h["gen"], old_gen, "the format-4 checkpoint was resumed");
    assert_eq!(reviewed(&tm), truth);
    assert_eq!(head(&tm)["gen"], h["gen"], "rebuilt once, not on every verb");
}

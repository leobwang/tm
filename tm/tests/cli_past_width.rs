//! **A duration past the host's width refuses the tree by name** — the
//! campaign's D69 call on README gap 3345 (stage 6 W-38 track T, parity P61;
//! `Width.lean`).
//!
//! `tm-core` holds a duration as `u32` minutes, so since W-37 (P57) a leading
//! estimate like `99999999999m` is `tm check`'s `bad-value` error — while the
//! kernel read any number and loaded, planned and closed the same tree. Now the
//! kernel's loader refuses it BY NAME (`pastWidth`, with the line and the slot),
//! at the host's width and the host's block length, and `tm check` names the
//! line as it names a key collision (D32). The same holds of `est:`, `dur:` and
//! `buffer:`, which the host reads with the same `Dur::parse`.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// `plan-basic` with `line` appended to `backlog.md`, and the 1-based line it lands on.
fn with_line(line: &str) -> (Tm, usize) {
    let tm = Tm::new();
    let path = tm.plan.join("backlog.md");
    let mut text = std::fs::read_to_string(&path).expect("backlog.md");
    if !text.ends_with('\n') {
        text.push('\n');
    }
    text.push_str(line);
    text.push('\n');
    std::fs::write(&path, &text).expect("backlog.md");
    let n = text.lines().count();
    (tm, n)
}

/// Every file of the plan directory and its bytes, for "nothing was written".
fn bytes(tm: &Tm) -> Vec<(String, Vec<u8>)> {
    let mut out = Vec::new();
    let mut stack = vec![tm.plan.clone()];
    while let Some(dir) = stack.pop() {
        for e in std::fs::read_dir(&dir).expect("a directory").flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
            } else {
                out.push((p.display().to_string(), std::fs::read(&p).expect("a file")));
            }
        }
    }
    out.sort();
    out
}

/// The `--json` error document a refused verb writes on stderr — after the
/// automatic close's own notice, which says the same refusal first.
fn err_doc(stderr: &str) -> Value {
    let at = if stderr.starts_with('{') { 0 } else { stderr.find("\n{").map_or(stderr.len(), |i| i + 1) };
    serde_json::from_str(&stderr[at..]).unwrap_or_else(|e| panic!("no JSON document on stderr ({e}): {stderr:?}"))
}

/// `tm check --json`'s problems at `backlog.md:line`, as `(code, message)`.
fn problems_at(tm: &Tm, line: usize) -> Vec<(String, String)> {
    let out = tm.run(&["--json", "check"]);
    let v: Value = serde_json::from_str(&out.stdout).unwrap_or_else(|e| panic!("{e}: {}", out.stdout));
    v["problems"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .filter(|p| p["file"] == "backlog.md" && p["line"].as_u64() == Some(line as u64))
        .map(|p| {
            (
                p["code"].as_str().unwrap_or_default().to_string(),
                p["message"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect()
}

/// **The drive, pinned, for each of the four slots.** `tm check` names the
/// line with the kernel's refusal beside its own `bad-value`; a kernel-backed
/// verb refuses by name, exits 1 and writes nothing; `--json` carries the
/// refusal, the line and the slot.
#[test]
fn a_duration_past_the_width_is_refused_by_name_at_its_line() {
    let cases = [
        ("- [ ] 2 99999999999m Big migration ^z9", "lead"),
        ("- [ ] 2 Big migration est:99999999999m ^z9", "est"),
        ("- [ ] 2 Big migration dur:4294967296m ^z9", "dur"),
        ("- [ ] 2 Big migration buffer:4294967296m ^z9", "buffer"),
    ];
    for (line, slot) in cases {
        let (tm, n) = with_line(line);
        let at = problems_at(&tm, n);
        assert!(
            at.iter().any(|(code, msg)| code == "kernel-load" && msg.contains("pastWidth")),
            "{line}: tm check names the line with the kernel's refusal: {at:?}"
        );
        let before = bytes(&tm);
        let out = tm.run(&["--json", "drop", "^a1"]);
        assert_eq!(out.code, 1, "{line}: {}{}", out.stdout, out.stderr);
        let v = err_doc(&out.stderr);
        assert_eq!(v["detail"]["refusal"], "pastWidth", "{line}: {v}");
        assert_eq!(v["detail"]["slot"], slot, "{line}: {v}");
        assert_eq!(v["detail"]["path"], "backlog.md", "{line}: {v}");
        assert_eq!(v["detail"]["line"], n as u64, "{line}: {v}");
        assert_eq!(bytes(&tm), before, "{line}: nothing was written");
    }
}

/// **The block length is the host's**: `71582789b` is 4,294,967,340 minutes at
/// `plan-basic`'s sixty-minute block and refused, where the numeral alone fits.
#[test]
fn a_block_estimate_is_measured_at_the_hosts_block_length() {
    let (tm, n) = with_line("- [ ] 2 71582789b Big migration ^z9");
    let out = tm.run(&["--json", "drop", "^a1"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let v = err_doc(&out.stderr);
    assert_eq!((v["detail"]["refusal"].as_str(), v["detail"]["line"].as_u64()), (Some("pastWidth"), Some(n as u64)), "{v}");
    assert!(
        problems_at(&tm, n).iter().any(|(code, msg)| code == "kernel-load" && msg.contains("pastWidth")),
        "tm check asks at the same block length: {:?}",
        problems_at(&tm, n)
    );
}

/// **The verb's own request carries the block length too.** Once the automatic
/// close has swept the tree (the first verb), a later `tm drop` asks the kernel
/// with its own request (`kernel_bridge::apply`) — no automatic close speaks
/// first — and that request reads `71582789b` at sixty minutes a block and is
/// refused; read at one minute a block it would have been loaded and written.
#[test]
fn the_verbs_own_request_reads_the_hosts_block_length() {
    let tm = Tm::new();
    tm.ok(&["now"]);
    let path = tm.plan.join("backlog.md");
    let mut text = std::fs::read_to_string(&path).expect("backlog.md");
    text.push_str("- [ ] 2 71582789b Big migration ^z9\n");
    std::fs::write(&path, &text).expect("backlog.md");
    let before = bytes(&tm);
    let out = tm.run(&["--json", "drop", "^a1"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("automatic close"), "the verb's own request refused: {}", out.stderr);
    let v = err_doc(&out.stderr);
    assert_eq!(v["detail"]["refusal"], "pastWidth", "{v}");
    assert_eq!(bytes(&tm), before, "nothing was written");
}

/// **It does not over-bite** (AGENTS §5.8): the width's last minute loads, and
/// a verb on that tree writes.
#[test]
fn the_widths_last_minute_loads() {
    let (tm, n) = with_line("- [ ] 2 4294967295m Big migration ^z9");
    assert!(problems_at(&tm, n).is_empty(), "{:?}", problems_at(&tm, n));
    let out = tm.run(&["drop", "^a1"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(tm.line("backlog.md", "a1").starts_with("- [~]"), "{}", tm.line("backlog.md", "a1"));
}

/// **The kernel's own WRITERS are held to the width too** (README gap 3520, the
/// W-38 repair). Before it, `tm edit ^a1 dur=4294967296m` wrote the line and
/// exited 0, and every kernel-backed verb then refused the tree `pastWidth`:
/// the loader knew the four slots and the edit writer bounded only `est`. Now
/// the keyed edit of `dur`, `buffer` and `est` is refused `badValue <key>` —
/// the name `est` was already refused by — at the host's block length, exit 1,
/// nothing written; and the width's last minute is written (§5.8).
#[test]
fn a_keyed_edit_past_the_width_is_refused_and_writes_nothing() {
    for (kv, key) in [
        ("dur=4294967296m", "dur"),
        ("buffer=4294967296m", "buffer"),
        ("dur=71582789b", "dur"),
        ("est=4294967296m", "est"),
    ] {
        let tm = Tm::new();
        // The Markdown only: the first verb's housekeeping may write `.tm/`
        // (the replay cache, D13; the close's sweep), which is not the edit.
        let md = |tm: &Tm| bytes(tm).into_iter().filter(|(p, _)| p.ends_with(".md")).collect::<Vec<_>>();
        let before = md(&tm);
        let out = tm.run(&["--json", "edit", "^a1", kv]);
        assert_eq!(out.code, 1, "{kv}: {}{}", out.stdout, out.stderr);
        let v = err_doc(&out.stderr);
        assert_eq!(v["detail"]["refusal"], "badValue", "{kv}: {v}");
        assert_eq!(v["detail"]["key"], key, "{kv}: {v}");
        assert_eq!(md(&tm), before, "{kv}: no Markdown was written");
        assert_eq!(tm.run(&["check"]).code, 0, "{kv}: the tree still loads");
    }
    let tm = Tm::new();
    let out = tm.run(&["edit", "^a1", "dur=4294967295m"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(tm.line("backlog.md", "a1").contains("dur:4294967295m"), "{}", tm.line("backlog.md", "a1"));
}

//! **T0, design §14.1 and D9-21: every recursion over a list the wire can make
//! large runs in constant stack per element.**  Its own test binary, not
//! `tests/kernel.rs`, because these requests are megabytes each.
//!
//! **`check.sh` check 5 runs this binary since the owner's D36** (stage 6 W-18
//! track A; README gap 686).  It ran `--test kernel` alone for four runs, and
//! the root `Cargo.toml` excludes this crate from the workspace, so every test
//! below was run by nothing automatic — a procedure, not a gate.  The header
//! used to say keeping them out *"keeps `check.sh`'s wall time inside design
//! §14.0 item 4's 10% budget"*, and that was true and was the reason: the file
//! costs **2.23 s** against a **3.8 s** built-tree wall, **+59%**.  The owner
//! declared that one-time payment rather than leave the file unguarded.
//! **A test added here is paid for by every `check.sh` from now on.**
//!
//! Stage 5 step A1 (gap 44 closed).  T0 (c) joined at L6 (gap 105 closed); T0 (b) joins at W3.
//! Stage 5 D9 B4 adds the `log` op at the line bound (`readLine`, `renderLine`).

use tm_kernel_ffi::call;

/// Runs `f` on a thread whose stack is exactly 2 MiB, so a test does not lean
/// on the harness's default (`RUST_MIN_STACK` can raise it).
fn on_a_2mib_thread<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// **T0 (a), design §14.1: gap 44 is closed.**  `jarr`/`jtail`, `jobj`/`jotail`,
/// `jemitTail`/`jemitOTail` and `splitDoc` recursed once per element, so before
/// A1 an array of 22,000 strings aborted a 2 MiB thread.  They now run as proved
/// `@[csimp]` accumulator twins (`jtail_eq_jtailAcc`, `jotail_eq_jotailAcc`,
/// `jemitTail_eq_jemitTailAcc`, `jemitOTail_eq_jemitOTailAcc`,
/// `splitDoc_eq_splitDocAcc`).  Arrays of strings: a 200,000-line document is
/// read, split, loaded, written and emitted back byte for byte.  Arrays of
/// objects: 200,000 objects are parsed to the end (the refusal is `run`'s, not
/// the parser's, and the same bytes with the closing `]` removed are refused by
/// the parser at the last element).  The objects sit in a key `run` never reads
/// because `run` appends each document with `++`, quadratic in the document
/// count (README "Stage 5 A1", gap 100).
#[test]
fn a_200000_element_array_reads_on_a_2mib_thread() {
    on_a_2mib_thread(|| {
        let lines: Vec<String> = (0..200_000).map(|i| format!("\"x{i}\"")).collect();
        let lines = lines.join(",");
        let out = call(&format!(r#"{{"docs":[{{"path":"w.md","lines":[{lines}]}}],"cmds":[]}}"#))
            .unwrap();
        assert_eq!(
            out,
            format!(r#"{{"ok":{{"docs":[{{"path":"w.md","lines":[{lines}]}}],"report":{{"closes":[]}}}}}}"#)
        );
    });
    on_a_2mib_thread(|| {
        let objs: Vec<String> =
            (0..200_000).map(|i| format!(r#"{{"path":"d{i}.md","lines":["x"]}}"#)).collect();
        let objs = objs.join(",");
        let out = call(&format!(r#"{{"docs":7,"pad":[{objs}]}}"#)).unwrap();
        assert_eq!(out, r#"{"err":"array expected"}"#);
        let out = call(&format!(r#"{{"docs":7,"pad":[{objs}}}"#)).unwrap();
        assert_eq!(out, r#"{"err":"bad json: expectedCommaOrBracket }"}"#);
    });
}

/// **T0 (a), the object half at scale (W-1 audit repair).**  The test above
/// sends 200,000 two-key objects, so `jotail` never runs past its second key.
/// Here the per-key twin `jotail_eq_jotailAcc` runs at scale: one object of
/// 200,000 keys, then 200,000 one-key objects, each on a 2 MiB thread, each in a
/// key `run` never reads, so the whole request is parsed and an empty `ok`
/// answers.  The same bytes with the object's closing `}` turned into `]` are
/// refused by the parser at the last key, so the parse did reach the end.
///
/// The emit twin `jemitOTail_eq_jemitOTailAcc` is not run at scale here, and
/// no wire request can run it: every object the kernel emits has a key list
/// written out in the source (`runPlanFast`, `reportJson`, `regionJson`,
/// `lerrJson`, `jone`), at most five keys, so `jemitOTail` never recurses more
/// than five times from `call`.  Large *arrays* are what a response carries,
/// and those are `jemitTail`, run by the test above.
#[test]
fn a_200000_key_object_reads_on_a_2mib_thread() {
    const EMPTY_OK: &str = r#"{"ok":{"docs":[],"report":{"closes":[]}}}"#;
    on_a_2mib_thread(|| {
        let keys: Vec<String> = (0..200_000).map(|i| format!(r#""k{i}":{i}"#)).collect();
        let keys = keys.join(",");
        let out = call(&format!(r#"{{"docs":[],"cmds":[],"pad":{{{keys}}}}}"#)).unwrap();
        assert_eq!(out, EMPTY_OK);
        let out = call(&format!(r#"{{"docs":[],"cmds":[],"pad":{{{keys}]}}"#)).unwrap();
        assert_eq!(out, r#"{"err":"bad json: expectedCommaOrBrace ]"}"#);
    });
    on_a_2mib_thread(|| {
        let objs: Vec<String> = (0..200_000).map(|i| format!(r#"{{"k":{i}}}"#)).collect();
        let objs = objs.join(",");
        let out = call(&format!(r#"{{"docs":[],"cmds":[],"pad":[{objs}]}}"#)).unwrap();
        assert_eq!(out, EMPTY_OK);
    });
}

/// A request of `lines` for the `log` op (stage 5 D9 B4), every line asked for a
/// header and, up to 4,096, a rendering; the zone is UTC with no transitions.
fn log_request(lines: &[String], render: usize) -> String {
    let render: Vec<String> = (1..=render.min(lines.len())).map(|n| n.to_string()).collect();
    format!(
        r#"{{"docs":[],"now":"2026-09-15","tz":{{"key":"UTC","base":"+00:00:00","then":[]}},"log":{{"ckpt":null,"from":1,"lines":[{}],"terminated":true,"want":{{"headersFrom":1,"render":[{}]}}}}}}"#,
        lines.join(","),
        render.join(",")
    )
}

/// **T0 for the `log` op (stage 5 D9 B4; README gap 101's note).**  `readLine`
/// and `renderLine` end to end on a 2 MiB thread, at the line bound: a string of
/// 65,000 characters, an unknown event's array of 21,000 numerals, an unknown
/// event of 5,000 keys (`restOf`'s merge sort, and `jemitOTail` at scale: the
/// rendering is an object of 5,002 keys, which the A1 test above could not reach
/// from `call`), 64 levels of nesting, an `hsw` of 65,000 fraction digits
/// (`finiteF64` and `JDec.render`), a line one character past the bound
/// (`lineTooLong`), and one nested 65 deep (`lineTooDeep`).  Then 8,192 lines,
/// the per-call bound (W3 lowered it from 32,768 by gap 102's memory gate), each with
/// a header, 4,096 of them rendered.  Since W3 a request asking for headers resumes, so it
/// carries `now` and the answer ends with `reseal`.
#[test]
fn the_log_op_reads_and_renders_at_the_line_bound_on_a_2mib_thread() {
    const T: &str = r#"\"t\":\"2026-09-07T06:05:00-05:00\""#;
    on_a_2mib_thread(|| {
        let nums = vec!["1"; 21_000].join(",");
        let keys: Vec<String> = (0..5_000).map(|i| format!(r#"\"k{i}\":{i}"#)).collect();
        let deep = format!("{}1{}", "[".repeat(63), "]".repeat(63));
        let lines = vec![
            format!(r#""{{{T},\"ev\":\"note\",\"text\":\"{}\"}}""#, "y".repeat(65_000)),
            format!(r#""{{{T},\"ev\":\"mood\",\"xs\":[{nums}]}}""#),
            format!(r#""{{{T},\"ev\":\"mood\",{}}}""#, keys.join(",")),
            format!(r#""{{{T},\"ev\":\"mood\",\"x\":{deep}}}""#),
            format!(r#""{{{T},\"ev\":\"energy\",\"pred\":1,\"rep\":1,\"hsw\":0.{}1,\"loc\":\"h\"}}""#, "0".repeat(65_000)),
            format!(r#""{{{T},\"ev\":\"note\",\"text\":\"{}\"}}""#, "y".repeat(65_537)),
            format!(r#""{{{T},\"ev\":\"mood\",\"x\":[{deep}]}}""#),
        ];
        let out = call(&log_request(&lines, 7)).unwrap();
        assert!(out.starts_with(r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"lines":7,"warnings":[{"line":6,"w":"lineTooLong"},{"line":7,"w":"lineTooDeep"}],"facts":null,"headers":[[1,"note",null,739865,false,"2026-09-07 06:05"],[2,"mood",null,739865,false,"2026-09-07 06:05"],[3,"mood",null,739865,false,"2026-09-07 06:05"],[4,"mood",null,739865,false,"2026-09-07 06:05"],[5,"energy",null,739865,false,"2026-09-07 06:05"]],"render":[[1,"{\"t\":\"2026-09-07T06:05:00-05:00\",\"ev\":\"note\",\"text\":\"yyy"#), "{}", &out[..out.len().min(400)]);
        assert!(out.contains(&format!(r#"\"hsw\":0.{}1,"#, "0".repeat(65_000))));
        assert!(out.contains(r#"\"k999\":999}"#), "the last key in serde's order");
        assert!(out.ends_with(r#""2026-09-07 06:05"],[6,null,null],[7,null,null]],"reseal":null}}}"#), "{}", &out[out.len().saturating_sub(200)..]);
    });
    on_a_2mib_thread(|| {
        let lines: Vec<String> = (0..8_192)
            .map(|i| format!(r#""{{{T},\"ev\":\"drop\",\"id\":\"x{i}\"}}""#))
            .collect();
        let out = call(&log_request(&lines, 4096)).unwrap();
        assert!(out.starts_with(r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"lines":8192,"warnings":[],"facts":null,"headers":[[1,"drop","x0",739865,false,"2026-09-07 06:05"],"#));
        assert!(out.contains(r#"[8192,"drop","x8191",739865,false,"2026-09-07 06:05"]],"render":[[1,"#));
        assert!(out.ends_with(r#"[4096,"{\"t\":\"2026-09-07T06:05:00-05:00\",\"ev\":\"drop\",\"id\":\"x4095\"}","2026-09-07 06:05"]],"reseal":null}}}"#));
        let mut one_more = lines.clone();
        one_more.push(r#""""#.to_string());
        assert_eq!(call(&log_request(&one_more, 0)).unwrap(), r#"{"err":{"log":"tooManyLines"}}"#);
    });
    // Stage 5 D9 C1: the undo mask at the line bound (`Replay.maskFast`, a `foldl`; the
    // `@[csimp]` twins `survivors_eq_survivorsFast` and `cancelledLines_eq_cancelledLinesFast`).
    // 4,096 drops, each followed by its undo: every line is cancelled (W3: the bound is 8,192 lines).
    on_a_2mib_thread(|| {
        let lines: Vec<String> = (0..8_192)
            .map(|i| {
                if i % 2 == 0 {
                    format!(r#""{{{T},\"ev\":\"drop\",\"id\":\"x{i}\"}}""#)
                } else {
                    format!(r#""{{{T},\"ev\":\"undo\",\"of\":\"drop\",\"id\":\"x{}\"}}""#, i - 1)
                }
            })
            .collect();
        let req = format!(
            r#"{{"docs":[],"now":"2026-09-15","tz":{{"key":"UTC","base":"+00:00:00","then":[]}},"log":{{"ckpt":null,"from":1,"lines":[{}],"terminated":true,"want":{{"facts":true}}}}}}"#,
            lines.join(",")
        );
        let start = std::time::Instant::now();
        let out = call(&req).unwrap();
        // C6 (design §8.4's view), in W3's codec shape: every line is cancelled, so no survivor writes a
        // record, a seam or an observation; the one day, 2026-09-07 (06:05 at -05:00 is 11:05 UTC, day
        // 739,865, second 63,924,375,900), holds the 8,192 headers, each cancelled, each with its stamp
        // and written offset. The answer's ledger day and horizon are the empty checkpoint's, 0.
        let headers: Vec<String> = (1..=8_192)
            .map(|n| {
                if n % 2 == 1 {
                    format!(r#"[{n},"drop","x{}",true,[63924375900,0],[true,18000]]"#, n - 1)
                } else {
                    format!(r#"[{n},"undo","x{}",true,[63924375900,0],[true,18000]]"#, n - 2)
                }
            })
            .collect();
        assert_eq!(
            out,
            format!(
                r#"{{"ok":{{"docs":[],"report":{{"closes":[]}},"log":{{"lines":8192,"warnings":[],"facts":{{"ledgerDay":0,"horizon":0,"items":[],"window":[],"instOther":[],"named":[],"days":[[739865,null,null,[],[],[],[],[],[{}]]],"open":{{"block":null,"interrupt":null}},"lastDay":null,"lastEffective":null,"entryCount":8192,"unknown":0,"longestLeak":null,"replayWarnings":[],"warnings":{{"first":[],"overflow":0}}}},"headers":[],"render":[],"reseal":null}}}}}}"#,
                headers.join(",")
            )
        );
        eprintln!("the mask at the line bound: {:.0} ms", start.elapsed().as_secs_f64() * 1000.0);
    });
    // Stage 5 D9 C2: the day index at the line bound (`Replay.sortWakes` compiled as
    // core's merge sort, `sortWakes_eq_sortWakesFast`; each entry's wake found by
    // bisection, `entryDays_eq_entryDaysFast`). 8,192 wakes on 8,192 dates written
    // newest first (W3: the bound is 8,192 lines), so the sort reverses the whole list and
    // the index keeps every wake; each wake is on its own date. Since W3 the facts come
    // from a resume from the empty checkpoint, in the codec's shape.
    on_a_2mib_thread(|| {
        let lines: Vec<String> = (0..8_192i64)
            .map(|i| format!(r#""{{\"t\":\"{}T06:05:00Z\",\"ev\":\"wake\",\"slept_min\":420}}""#, date_after_spec_monday(-i)))
            .collect();
        let req = format!(
            r#"{{"docs":[],"now":"2026-09-15","tz":{{"key":"UTC","base":"+00:00:00","then":[]}},"log":{{"ckpt":null,"from":1,"lines":[{}],"terminated":true,"want":{{"facts":true}}}}}}"#,
            lines.join(",")
        );
        let start = std::time::Instant::now();
        let out = call(&req).unwrap();
        // C6 (design §8.4's view): every wake creates its day. Each day's record is
        // `DayReplay::new`'s block fields, the wake (06:05 UTC) and its sleep, 420; its seam's
        // latest stamp is the wake; its one header is the wake's, on its own date.
        assert!(out.starts_with(r#"{"ok":{"docs":[],"report":{"closes":[]},"log":{"lines":8192,"warnings":[],"facts":{"ledgerDay":0,"horizon":0,"items":[],"window":[],"instOther":[],"named":[],"days":[["#), "{}", &out[..out.len().min(400)]);
        assert_eq!(
            out.matches(r#",[null,[],0,0,0,[0,0,0,0,0,0],[],[],0,[],[],["#).count(),
            8_192,
            "one day record a wake, its block fields empty"
        );
        assert_eq!(out.matches(r#",0,false,0],420,null,null,null,null,null,[],0,0,[],[],0,0,0,0,null],[null,[],["#).count(), 8_192, "its wake, its sleep and its seam");
        assert_eq!(out.matches(r#",0,false,0]],[],[],[],[],[],[["#).count(), 8_192, "no observation, interruption, demotion or close; its header");
        for i in [0i64, 1, 4_095, 8_191] {
            let d = 739_865 - i;
            let sec = d * 86_400 + 6 * 3_600 + 5 * 60;
            let line = i + 1;
            assert!(out.contains(&format!(r#"[{d},[null,[],0,0,0,"#)), "the day record of day {d}");
            assert!(out.contains(&format!(r#"[{sec},0,false,0],420,null,"#)), "the wake of day {d}");
            assert!(out.contains(&format!(r#",[[{line},"wake",null,false,"#)), "the header of line {line}");
        }
        // The last survivor in file order is line 8,192's wake, 06:05 UTC on day 739,865 − 8,191,
        // and the last day is 739,865.
        let last: i64 = (739_865 - 8_191) * 86_400 + 6 * 3_600 + 5 * 60;
        assert!(
            out.ends_with(&format!(
                r#"]]]],"open":{{"block":null,"interrupt":null}},"lastDay":739865,"lastEffective":[{last},0,false,0],"entryCount":8192,"unknown":0,"longestLeak":null,"replayWarnings":[],"warnings":{{"first":[],"overflow":0}}}},"headers":[],"render":[],"reseal":null}}}}}}"#
            )),
            "{}",
            &out[out.len().saturating_sub(400)..]
        );
        eprintln!("the day index at the line bound: {:.0} ms, {} bytes", start.elapsed().as_secs_f64() * 1000.0, out.len());
    });
    // Stage 5 D9 C3: the block machine at the line bound (`Replay.replay`, compiled as
    // `Replay.replayFast`: one `foldl` of the effects over the survivors, maps altered by a
    // tail-recursive loop, the observations and each day's segments sorted by core's merge
    // sort through `sortObs_eq_sortObsFast` and `sortSegs_eq_sortSegsFast`). 4,096 blocks of
    // one item (W3: the bound is 8,192 lines), a `start` and a one-minute `done` two minutes
    // apart, over 6 days: 4,096 segments, observations, durations and completions.
    on_a_2mib_thread(|| {
        let stamp = |i: i64, plus: i64| {
            let m = (i % 720) * 2 + plus;
            format!(r#"\"t\":\"{}T{:02}:{:02}:00Z\""#, date_after_spec_monday(i / 720), m / 60, m % 60)
        };
        let lines: Vec<String> = (0..4_096i64)
            .flat_map(|i| {
                [
                    format!(r#""{{{},\"ev\":\"start\",\"id\":\"a\",\"pred\":3,\"rep\":3,\"loc\":\"h\"}}""#, stamp(i, 0)),
                    format!(r#""{{{},\"ev\":\"done\",\"id\":\"a\",\"est_min\":1,\"actual_min\":1,\"ci\":3}}""#, stamp(i, 1)),
                ]
            })
            .collect();
        let req = format!(
            r#"{{"docs":[],"now":"2026-09-15","tz":{{"key":"UTC","base":"+00:00:00","then":[]}},"log":{{"ckpt":null,"from":1,"lines":[{}],"terminated":true,"want":{{"facts":true}}}}}}"#,
            lines.join(",")
        );
        let start = std::time::Instant::now();
        let out = call(&req).unwrap();
        // C6 (design §8.4's view), in W3's codec shape (a segment's kind is `[0, id]` for a block).
        assert!(out.contains(r#""items":[["a",[4096,4096,[["#), "{}", &out[..out.len().min(400)]);
        assert_eq!(out.matches(r#",[0,"a"]]"#).count(), 4_096, "one segment a block");
        assert_eq!(out.matches(r#",739865,3,3,0.0,"h",0,null,"a",true]"#).count(), 720, "the first day's start observations");
        // C4: every `done` completes `a`, so its done dates are the 6 days (its first the 7th,
        // 6 of them), and its `last_done` is the last `done` (block 4,095: day 739,870 at 16:31).
        assert!(out.contains(r#",0,0],[63924827460,0,false,0],false,739865,6]],"window":["#), "{}", &out[..out.len().min(600)]);
        assert!(out.contains(r#""open":{"block":null,"interrupt":null},"lastDay":739870,"lastEffective":[63924827460,0,false,0],"#), "{}", &out[out.len().saturating_sub(600)..]);
        for d in 739_865..=739_870 {
            assert!(out.contains(&format!(r#"[{d},[["a","#)), "the window of day {d}");
        }
        // C5: the 6 days' records hold nothing of the day family (no wake, arrival, gap or plan).
        assert_eq!(out.matches(r#",null,null,null,null,null,null,null,[],0,0,[],[],0,0,0,0,null],["#).count(), 6, "6 day records empty of the day family");
        assert!(out.ends_with(r#""unknown":0,"longestLeak":null,"replayWarnings":[],"warnings":{"first":[],"overflow":0}},"headers":[],"render":[],"reseal":null}}}"#), "{}", &out[out.len().saturating_sub(300)..]);
        eprintln!("the block machine at the line bound: {:.0} ms, {} bytes", start.elapsed().as_secs_f64() * 1000.0, out.len());
    });
    // Stage 5 D9 C4: the completion family at the line bound (the same `foldl`; instances,
    // done dates and `LatestNamed` records altered in `Replay.HMap`'s buckets, sized to the
    // log). 4,096 `routine` lines of one item, each on its own instance, the even ones
    // `done` and the odd ones `maybe` (a replay warning each), then 4,096 `event` lines
    // over 64 names, all at 06:05 on 2026-09-07 written in UTC (W3: the bound is 8,192 lines).
    on_a_2mib_thread(|| {
        let lines: Vec<String> = (0..4_096)
            .map(|i| {
                format!(
                    r##""{{\"t\":\"2026-09-07T06:05:00Z\",\"ev\":\"routine\",\"item\":\"r\",\"inst\":\"#{i}\",\"status\":\"{}\"}}""##,
                    if i % 2 == 0 { "done" } else { "maybe" }
                )
            })
            .chain((0..4_096).map(|i| format!(r#""{{\"t\":\"2026-09-07T06:05:00Z\",\"ev\":\"event\",\"name\":\"n{}\"}}""#, i % 64)))
            .collect();
        let req = format!(
            r#"{{"docs":[],"now":"2026-09-15","tz":{{"key":"UTC","base":"+00:00:00","then":[]}},"log":{{"ckpt":null,"from":1,"lines":[{}],"terminated":true,"want":{{"facts":true}}}}}}"#,
            lines.join(",")
        );
        let start = std::time::Instant::now();
        let out = call(&req).unwrap();
        let ms = start.elapsed().as_secs_f64() * 1000.0;
        let t = r#"[63924357900,0,false,0]"#;
        // W3's codec shape: an instance is `[[item, inst], [stamp, status, raw, actualMin]]`, its status a numeral
        // (done 0, pending 1); a replay warning is `[line, raw]`.
        assert_eq!(out.matches(r##"[["r","#"##).count(), 4_096, "one instance a routine line");
        assert_eq!(out.matches(&format!(r#"{t},0,"done",null]"#)).count(), 2_048);
        assert_eq!(out.matches(&format!(r#"{t},1,"maybe",null]"#)).count(), 2_048);
        assert_eq!(out.matches(r#","maybe"]"#).count(), 2_048);
        // The first `done` of equal instants is `last_done`; every one is on the day.
        assert!(out.contains(&format!(r#""items":[["r",null,{t},false,739865,1]],"#)), "{}", &out[..out.len().min(600)]);
        // Each name's latest by instant and by date is its last line (a later line wins a tie).
        for k in 0..64 {
            let last = 4_096 + 4_032 + k + 1;
            assert!(out.contains(&format!(r#"[["n{k}",null],[[{last},{t}],[739865,[{last},{t}]]]]"#)), "name n{k}");
        }
        assert!(out.contains(r#""replayWarnings":[[2,"maybe"],[4,"maybe"],"#));
        eprintln!("the completion family at the line bound: {ms:.0} ms (the call), {} bytes", out.len());
    });
}

/// `YYYY-MM-DD` of day `n` after 2026-09-07 (Howard Hinnant's `civil_from_days`,
/// over days since 1970-01-01; 2026-09-07 is day 20,703).
fn date_after_spec_monday(n: i64) -> String {
    let z = 20_703 + n + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + if m <= 2 { 1 } else { 0 };
    format!("{y:04}-{m:02}-{d:02}")
}

/// **T0 (c), design §14.8's L5 row, committed at L6 (gap 105 closed).**  The
/// lookahead of 3,660 days (`Look.maxLookaheadDays`) runs on a 2 MiB thread,
/// through the wire: a zone table of 600 transitions (a Chicago-shaped pair every
/// year over [1900, 2200)), and a calendar wall 12:50–13:50 on every one of the
/// 3,660 days, each indexed once by `wallIndex` and filtered per day by
/// `wallsOn`.  The day range is a `foldl` over core's `List.range`, each day held
/// once (`dayOf_eq_dayOfFast`), and every day is computed before the first seven
/// are emitted (Lean is strict).  The first seven days equal a seven-day request's.
#[test]
fn a_3660_day_lookahead_runs_on_a_2mib_thread() {
    let mut then = Vec::new();
    for y in 1900..2200 {
        then.push(format!(r#"["{y}-03-08T08:00:00Z","-05:00:00"]"#));
        then.push(format!(r#"["{y}-11-01T07:00:00Z","-06:00:00"]"#));
    }
    assert_eq!(then.len(), 600);
    let tz = format!(r#""tz":{{"key":"Chicago-shaped|1900-2200","base":"-06:00:00","then":[{}]}}"#, then.join(","));
    let walls: Vec<String> = (0..3660)
        .map(|i| format!(r#""- [ ] 3 Meeting      at:{d}T12:50/13:50 ^w{i}""#, d = date_after_spec_monday(i)))
        .collect();
    let docs = format!(r#"{{"path":"calendar/walls.md","lines":[{}]}}"#, walls.join(","));
    let capacity = |days: u32| {
        format!(
            concat!(
                r#""capacity":{{"pLounge":{{"config":{{"Mon":{{"num":"9","den":"10"}},"Tue":{{"num":"9","den":"10"}},"Wed":{{"num":"9","den":"10"}},"Thu":{{"num":"9","den":"10"}},"Fri":{{"num":"8","den":"10"}},"Sat":{{"num":"5","den":"10"}},"Sun":{{"num":"4","den":"10"}}}}}},"#,
                r#""arrival":{{"config":{{"Mon":"07:00","Tue":"07:00","Wed":"07:00","Thu":"07:00","Fri":"07:00","Sat":"10:00","Sun":"10:00"}}}},"#,
                r#""wake":{{"sec":21940,"ns":250000000}},"#,
                r#""prior":{{"lounge":[{{"from":{{"num":0,"den":1}},"to":{{"num":1,"den":1}},"level":4}},{{"from":{{"num":1,"den":1}},"to":{{"num":5,"den":1}},"level":5}},{{"from":{{"num":5,"den":1}},"to":{{"num":8,"den":1}},"level":4}},{{"from":{{"num":8,"den":1}},"to":{{"num":10,"den":1}},"level":3}},{{"from":{{"num":10,"den":1}},"level":2}}],"#,
                r#""home":[{{"from":{{"num":0,"den":1}},"to":{{"num":1,"den":1}},"level":3}},{{"from":{{"num":1,"den":1}},"to":{{"num":4,"den":1}},"level":4}},{{"from":{{"num":4,"den":1}},"to":{{"num":8,"den":1}},"level":3}},{{"from":{{"num":8,"den":1}},"level":2}}]}},"#,
                r#""homeMaxCi":3,"day":{{"breakMin":20,"breakAfterBlocks":2,"minLastBlockMin":30,"windowHours":{{"num":8,"den":1}},"windowCap":"19:00","budgetRatio":{{"num":75,"den":100}},"windDown":"21:30","bed":"22:00"}},"#,
                r#""priority":{{"bins":[{{"num":5,"den":10}},{{"num":25,"den":100}},{{"num":1,"den":10}}],"safety":{{"num":13,"den":10}},"defaultPriority":3}},"#,
                r#""days":{days},"at":"2026-09-07T07:00:00-05:00","#,
                r#""state":{{"date":null,"window":null,"budget":null,"arrival":null,"loc":"lounge","allowHome":false}},"#,
                r#""posterior":{{"fullHours":{{"num":3,"den":1}},"zeroHours":{{"num":6,"den":1}}}},"#,
                r#""sleep":{{"shiftModel":null,"shiftConfig":{{"neg":false,"num":1,"den":1}},"underHours":{{"num":7,"den":1}}}}}}"#
            ),
            days = days
        )
    };
    let request = |days: u32| format!(r#"{{"docs":[{docs}],"now":"2026-09-07","blockMin":60,{tz},{CAP_LOG},{}}}"#, capacity(days));
    let long = request(3660);
    let week = request(7);
    on_a_2mib_thread(move || {
        let t = std::time::Instant::now();
        let out = call(&long).unwrap();
        let ms = t.elapsed().as_millis();
        assert!(out.starts_with(r#"{"ok":{"docs":[{"path":"calendar/walls.md""#), "{}", &out[..200.min(out.len())]);
        let look = &out[out.find(r#""lookahead":"#).expect("lookahead key")..];
        assert_eq!(look.matches(r#""day":"#).count(), 7, "{look}");
        let t = std::time::Instant::now();
        let short = call(&week).unwrap();
        let short_ms = t.elapsed().as_millis();
        let short_look = &short[short.find(r#""lookahead":"#).unwrap()..];
        assert_eq!(look, short_look);
        eprintln!("T0 (c): 3,660 days, 600 transitions, 3,660 walls: {ms} ms; the same request for 7 days: {short_ms} ms (2 MiB thread)");
    });
}

/// **The `log` section every capacity request carries since step L9** (gap 93): day 0 is derived
/// from the replay of the same call (D24's seam), so a capacity request without one is refused
/// `day0WithoutLog`.
const CAP_LOG: &str =
    r#""log":{"ckpt":null,"from":1,"lines":[],"terminated":true,"reseal":null,"want":{"facts":true,"headersFrom":null,"render":[]},"sealed":null}"#;

/// The T0 (c) request's capacity section (no calendar), with `candidates` when
/// `cands` is non-empty.
fn grants_request(days: u32, cands: &[String]) -> String {
    grants_request_docs(days, "", cands)
}

/// The same, over a tree: `docs` is the `docs` array's contents, so a caller can
/// ask what one call costs on a real plan rather than on no plan at all.
fn grants_request_docs(days: u32, docs: &str, cands: &[String]) -> String {
    let mut then = Vec::new();
    for y in 1900..2200 {
        then.push(format!(r#"["{y}-03-08T08:00:00Z","-05:00:00"]"#));
        then.push(format!(r#"["{y}-11-01T07:00:00Z","-06:00:00"]"#));
    }
    let tz = format!(r#""tz":{{"key":"Chicago-shaped|1900-2200","base":"-06:00:00","then":[{}]}}"#, then.join(","));
    let candidates = if cands.is_empty() {
        String::new()
    } else {
        format!(r#","candidates":{{"hysteresis":true,"items":[{}]}}"#, cands.join(","))
    };
    format!(
        concat!(
            r#"{{"docs":[{docs}],"now":"2026-09-07","blockMin":60,{tz},{cap_log},"#,
            r#""capacity":{{"pLounge":{{"config":{{"Mon":{{"num":"9","den":"10"}},"Tue":{{"num":"9","den":"10"}},"Wed":{{"num":"9","den":"10"}},"Thu":{{"num":"9","den":"10"}},"Fri":{{"num":"8","den":"10"}},"Sat":{{"num":"5","den":"10"}},"Sun":{{"num":"4","den":"10"}}}}}},"#,
            r#""arrival":{{"config":{{"Mon":"07:00","Tue":"07:00","Wed":"07:00","Thu":"07:00","Fri":"07:00","Sat":"10:00","Sun":"10:00"}}}},"#,
            r#""wake":{{"sec":21940,"ns":250000000}},"#,
            r#""prior":{{"lounge":[{{"from":{{"num":0,"den":1}},"to":{{"num":1,"den":1}},"level":4}},{{"from":{{"num":1,"den":1}},"to":{{"num":5,"den":1}},"level":5}},{{"from":{{"num":5,"den":1}},"to":{{"num":8,"den":1}},"level":4}},{{"from":{{"num":8,"den":1}},"to":{{"num":10,"den":1}},"level":3}},{{"from":{{"num":10,"den":1}},"level":2}}],"#,
            r#""home":[{{"from":{{"num":0,"den":1}},"to":{{"num":1,"den":1}},"level":3}},{{"from":{{"num":1,"den":1}},"to":{{"num":4,"den":1}},"level":4}},{{"from":{{"num":4,"den":1}},"to":{{"num":8,"den":1}},"level":3}},{{"from":{{"num":8,"den":1}},"level":2}}]}},"#,
            r#""homeMaxCi":3,"day":{{"breakMin":20,"breakAfterBlocks":2,"minLastBlockMin":30,"windowHours":{{"num":8,"den":1}},"windowCap":"19:00","budgetRatio":{{"num":75,"den":100}},"windDown":"21:30","bed":"22:00"}},"#,
            r#""priority":{{"bins":[{{"num":5,"den":10}},{{"num":25,"den":100}},{{"num":1,"den":10}}],"safety":{{"num":13,"den":10}},"defaultPriority":3}},"#,
            r#""days":{days},"at":"2026-09-07T07:00:00-05:00","#,
            r#""state":{{"date":null,"window":null,"budget":null,"arrival":null,"loc":"lounge","allowHome":false}},"#,
            r#""posterior":{{"fullHours":{{"num":3,"den":1}},"zeroHours":{{"num":6,"den":1}}}},"#,
            r#""sleep":{{"shiftModel":null,"shiftConfig":{{"neg":false,"num":1,"den":1}},"underHours":{{"num":7,"den":1}}}}{candidates}}}}}"#
        ),
        tz = tz,
        docs = docs,
        cap_log = CAP_LOG,
        days = days,
        candidates = candidates
    )
}

/// Section 8.2 step 5's nine candidate facts, all plain — `Look.wfUnconstrained`:
/// nothing planned, multiplier 1, no `loc:`, splittable, no `max:`, `[ ]`, no
/// unsatisfied dependency, not today's wall.
///
/// **It is REQUIRED on every candidate since stage 6 P5a (`f84d8cf`, README gap
/// 606); a candidate without it is refused `badCandidate <i> plan`** and the
/// call answers no `grants` at all.  These tests sent nine-field candidates and
/// three of the seven in this file failed on exactly that at W-18's land step —
/// the FIRST thing the owner's **D36** gate caught, and it could not have been
/// caught earlier because until D36 this file ran in no automated gate at all
/// (README gaps 686, 770).
///
/// **This is the SECOND spelling of this constant**: `tests/kernel.rs` holds the
/// first, by the same name.  They are separate test binaries with no shared
/// fixture module (only `corpus.rs` includes `tests/harness/mod.rs`), so the two
/// must be edited together whenever the nine change — README gap 771.
const PLAIN_PLAN: &str = r#""plan":{"plannedMin":0,"multiplier":{"num":1,"den":1},"loc":"any","splittable":true,"cap":null,"state":" ","blockedBy":[],"wallToday":false}"#;

/// `n` dated candidates at `ci` 3, 600 minutes each, due dates spread evenly
/// over `days` (the shape README gap 106 was measured with), and the nine plain.
fn spread_deadlines(n: usize, days: i64) -> Vec<String> {
    (0..n)
        .map(|i| {
            let due = date_after_spec_monday(((i as i64 + 1) * days) / n as i64 - 1);
            format!(
                r#"{{"id":"d{i}","ci":3,"remaining":600,"due":"{due}","window":false,"wall":false,"optional":false,"overdue":false,"mandatory":false,"hot":false,{PLAIN_PLAN}}}"#
            )
        })
        .collect()
}

/// **Gap 106, T0 for the EDF pass (stage 5 D10 L8).**  Step 3's `reserveRest`
/// read each day through one closure per earlier reservation, and its day
/// recursions were not tail calls; the pass now runs as a proved `@[csimp]`
/// `foldl` holding each reserved day's six numerators once
/// (`edfGrantsGo_eq_edfGrantsGoFast`).  Through the wire, on a 2 MiB thread:
/// 1, 10, 20, 30 and 40 deadlines over the 3,660-day lookahead (the gap's
/// shape), then 1,024 (`maxCandidates`, the wire's bound).  Each answer carries
/// one grant per candidate, and a deadline's grant does not depend on the
/// deadlines due after it (`edf_a_later_deadline_takes_nothing_from_an_earlier_one`).
///
/// **The time is asserted** (W-3's audit: the test only printed it, and with the
/// seven `@[csimp]` attributes removed 40 deadlines took 18,102 ms and it still
/// passed).  Each call must finish within `GAP_106_MS` for up to 40 deadlines
/// and `GAP_106_MAX_MS` for 1,024; measured 121 ms and 825 ms with the twins,
/// so the bounds leave a loaded machine 40x and 18x, and the bound for 40 is 3.6x
/// under the regression it guards (which grows as the fourth power of the count).
#[test]
fn grants_over_a_3660_day_lookahead_run_on_a_2mib_thread() {
    const GAP_106_MS: u128 = 5_000;
    const GAP_106_MAX_MS: u128 = 15_000;
    on_a_2mib_thread(|| {
        let base = grants_request(3660, &[]);
        let t = std::time::Instant::now();
        let out = call(&base).unwrap();
        let base_ms = t.elapsed().as_millis();
        assert!(!out.contains(r#""grants""#), "{}", &out[..200.min(out.len())]);
        let mut line = format!("gap 106: no candidates {base_ms} ms");
        let grant_of = |out: &str, id: &str| -> String {
            let grants = &out[out.find(r#""grants":"#).unwrap_or_else(|| panic!("{}", &out[..300.min(out.len())]))..];
            let at = grants.find(&format!(r#"{{"id":"{id}""#)).unwrap_or_else(|| panic!("{id}"));
            grants[at..].split('}').next().unwrap().to_string()
        };
        for n in [1usize, 10, 20, 30, 40, 1024] {
            let cands = spread_deadlines(n, 3660);
            let req = grants_request(3660, &cands);
            let t = std::time::Instant::now();
            let out = call(&req).unwrap();
            let ms = t.elapsed().as_millis();
            let bound = if n <= 40 { GAP_106_MS } else { GAP_106_MAX_MS };
            assert!(ms <= bound, "gap 106 regressed: {n} deadlines over 3,660 days took {ms} ms (bound {bound} ms)");
            let grants = &out[out.find(r#""grants":"#).unwrap_or_else(|| panic!("{}", &out[..300.min(out.len())]))..];
            assert_eq!(grants.matches(r#"{"id":"#).count(), n, "{}", &grants[..300.min(grants.len())]);
            // The first-due deadline is served first: its grant is the one it gets alone.
            let alone = call(&grants_request(3660, &cands[..1])).unwrap();
            assert_eq!(grant_of(&out, "d0"), grant_of(&alone, "d0"));
            line.push_str(&format!("; {n} deadlines {ms} ms"));
        }
        eprintln!("{line} (3,660 days, 2 MiB thread)");
    });
}

/// **The floor pass forces the capacity the pass left once per request** (stage 5
/// D10 L8, host half; gap 79).  `withFloor` takes that capacity as a `Thunk`: a
/// strict argument evaluated per candidate ran step 3's pass once per candidate,
/// and 1,024 of them over 3,660 days took 705 s of this suite.  Through the wire,
/// on a 2 MiB thread: 512 dated deadlines and 512 undated candidates with a floor
/// to the lookahead's last day, against the same 1,024 without the floors.  Every
/// floor candidate is answered at its floor, and the dated grants are the same
/// bytes either way (a floor reserves nothing).
#[test]
fn floors_over_a_3660_day_lookahead_force_the_pass_once() {
    on_a_2mib_thread(|| {
        let last = date_after_spec_monday(3659);
        let dated = spread_deadlines(512, 3660);
        let floors: Vec<String> = (0..512)
            .map(|i| {
                format!(
                    r#"{{"id":"f{i}","ci":{},"remaining":60,"due":null,"window":false,"wall":false,"optional":false,"overdue":false,"mandatory":false,"hot":false,{PLAIN_PLAN},"floor":{{"left":{},"until":"{last}"}}}}"#,
                    i % 6,
                    30 + i
                )
            })
            .collect();
        let bare: Vec<String> = floors.iter().map(|f| f.replace(&format!(r#","floor":{{"left":"#), r#","nofloor":{"left":"#)).collect();
        let with = [dated.clone(), floors].concat();
        let without = [dated, bare].concat();
        let t = std::time::Instant::now();
        let a = call(&grants_request(3660, &with)).unwrap();
        let with_ms = t.elapsed().as_millis();
        let t = std::time::Instant::now();
        let b = call(&grants_request(3660, &without)).unwrap();
        let without_ms = t.elapsed().as_millis();
        // Asserted, as gap 106's test is (W-3): 1,076 and 381 ms measured; forcing the
        // pass once per candidate took 705 s.
        assert!(with_ms <= 20_000 && without_ms <= 20_000, "floors {with_ms} ms, without {without_ms} ms (bound 20,000 ms)");
        let grants = |out: &str| out[out.find(r#""grants":"#).expect("grants")..].to_string();
        let (ga, gb) = (grants(&a), grants(&b));
        assert_eq!(ga.matches(r#""class":"#).count(), 1024);
        assert_eq!(ga.matches(&format!(r#""until":"{last}""#)).count() >= 512, true, "{}", &ga[..300]);
        let dated_part = |g: &str| g[..g.find(r#"{"id":"f0""#).expect("f0")].to_string();
        assert_eq!(dated_part(&ga), dated_part(&gb), "a floor reserves nothing");
        assert!(!gb.contains(r#""class":"floor""#));
        eprintln!("floors: 512 deadlines + 512 floors {with_ms} ms; the same without floors {without_ms} ms (3,660 days, 2 MiB thread)");
    });
}

// ---------------------------------------------------------------------------
// T17 — the replan the TUI would make on a tick (stage 6 W-17, step P4;
// design §20 gap 257, owner question Q8 / D30)
//
// **It was called T12 for one run, and T12 was taken** (README gap 688, closed
// at W-18 track A).  The campaign's instrument numbers are ONE sequence, not
// one per design document: T0-T16 are all claimed, T12 is
// `model_fit_is_the_fork_points_on_the_corpus` (stage-5 design §14.6,
// `cli_switch_acceptance.rs`) and T14 is
// `a_plan_with_a_due_three_and_ten_years_out_stays_a_later_verb`
// (`tm/tests/cli_latency.rs:310`), which is why the gap's own suggestion of
// T14 could not be taken either.  **T17 was free and is the first number that
// was.**  Before taking a number, find the highest MENTIONED and then check
// that one is free -- the README's newest block names the next free number, so
// the highest mentioned is usually it rather than a taken one:
//
//     grep -rhoE '\bT[0-9]+\b' kernel/README.md kernel/design | sort -uV | tail -1
//     grep -rn '\bT<n>\b' . | grep -v ^./target        # must find no instrument
//
// README gap 733 asks for a roster, next to gap 226's for the parity numbers,
// so that this is a lookup rather than two greps.
// ---------------------------------------------------------------------------

/// §9.1's stop condition: the TUI replans on a **tick** while a replan stays
/// under this, and on **reload** otherwise.  It is a budget to report against,
/// never a bound to assert: a test that failed here would be a latency band
/// re-blessed under another name.
const TUI_TICK_BUDGET_MS: u128 = 5;

/// The candidate count §9.1's figure was never taken at.
const REPLAN_CANDS: usize = 500;

/// `n` plain backlog items in `f` files — the shape of a busy plan, without
/// walls or dated lines, so the number below is the *tree* half of a call and
/// nothing else.
fn backlog_docs(files: usize, per: usize) -> String {
    (0..files)
        .map(|f| {
            let lines: Vec<String> = (0..per)
                .map(|j| format!(r#""- [ ] {} Task {f}-{j} ^t{f}x{j}""#, (f + j) % 6))
                .collect();
            format!(r#"{{"path":"plan/backlog{f}.md","lines":[{}]}}"#, lines.join(","))
        })
        .collect::<Vec<_>>()
        .join(",")
}

/// Best and median of `n` calls, in milliseconds, with the last answer.
fn time_call(req: &str, n: usize) -> (f64, f64, String) {
    let mut ms: Vec<f64> = Vec::with_capacity(n);
    let mut last = String::new();
    for _ in 0..n {
        let t = std::time::Instant::now();
        last = call(req).unwrap();
        ms.push(t.elapsed().as_secs_f64() * 1000.0);
    }
    let mut sorted = ms.clone();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (sorted[0], sorted[sorted.len() / 2], last)
}

/// **T17: what one replan costs through the FFI, at 500 candidates.**
///
/// **Why this exists.** `kernel/design/stage6/stage6-planner-design.md` §9.1
/// gives the TUI a 5 ms stop condition for replanning on a tick, and §20 gap
/// 257 records that **nothing in the tree measures one**: the 0.8 ms behind
/// that budget was taken at the FFI spike, against a kernel that did not exist
/// yet.  Owner decision D30 (Q8) makes the measurement step P4's, so that the
/// trigger has a number before it can fire.  The rule that comes with it is
/// D18's: *if the measurement exceeds 5 ms the fallback is to replan on reload,
/// never to raise the budget.*
///
/// **What it measures, and what it does not.** There is still **no planner op
/// on the wire** — `dayPlan` has no boundary op and no shipped caller (stage 6
/// W-16's block says so and W-17's repeats the grep) — so the request below is
/// the one a replan makes *today*: the `capacity` + `log` call, whole tree,
/// 7-day lookahead, `candidates` with 500 items, which is what
/// `TM_TRACE_KERNEL_CALLS=1 tm plan` prints (`log`, then `capacity+log`).  Its
/// §7 half — the EDF pass, the bins, the rows and the hysteresis — is exactly
/// what §8.2 step 4 runs, because `Planner.PlanReq.candAnswers` **is**
/// `Look.prioritiesWithFloors` at the same arguments
/// (`candAnswers_is_the_capacity_ops_own_grants`).  What is **not** in the
/// number is steps 5–8, which are not written.  So this is a **lower bound** on
/// a kernel replan, and the block that quotes it says so.
///
/// Three rows, so the cost can be attributed rather than guessed:
/// (a) 500 candidates, no documents — §7's pass alone;
/// (b) a 2,000-line tree, no candidates — the load alone;
/// (c) both — the call itself.
///
/// The assertion is a **regression** bound, 40x the measured (c), not the
/// budget.
#[test]
fn a_500_candidate_replan_through_the_ffi() {
    const REGRESSION_MS: u128 = 4_000;
    on_a_2mib_thread(|| {
        let cands = spread_deadlines(REPLAN_CANDS, 7);
        let docs = backlog_docs(100, 20);
        let big = grants_request_docs(7, &docs, &cands);
        let (pass_best, pass_med, pass_out) = time_call(&grants_request(7, &cands), 7);
        let (tree_best, tree_med, tree_out) = time_call(&grants_request_docs(7, &docs, &[]), 7);
        let (all_best, all_med, all_out) = time_call(&big, 7);
        // (d) the shape a real user has today: `tm init --example` is five files
        // of a handful of lines, and a day's queue is tens of candidates, not 500.
        let small = backlog_docs(5, 8);
        let few = spread_deadlines(50, 7);
        let (few_best, few_med, few_out) = time_call(&grants_request_docs(7, &small, &few), 7);

        // Each answer is the real one: 500 grants, and the tree comes back whole.
        for out in [&pass_out, &all_out] {
            let grants = &out[out.find(r#""grants":"#).expect("grants")..];
            assert_eq!(grants.matches(r#"{"id":"#).count(), REPLAN_CANDS, "500 grants");
        }
        {
            let grants = &few_out[few_out.find(r#""grants":"#).expect("grants")..];
            assert_eq!(grants.matches(r#"{"id":"#).count(), 50, "50 grants");
        }
        assert!(!tree_out.contains(r#""grants""#), "no candidates, no grants");
        for out in [&tree_out, &all_out] {
            assert_eq!(out.matches(r#""path":"plan/backlog"#).count(), 100, "the tree came back");
            assert!(out.contains(r#"^t99x19"#), "the last line came back");
        }

        assert!(
            (all_med as u128) <= REGRESSION_MS,
            "a 500-candidate replan took {all_med:.1} ms (regression bound {REGRESSION_MS} ms)"
        );
        eprintln!(
            "T17 replan through the FFI, 2 MiB thread, best/median of 7: \
             (a) {REPLAN_CANDS} candidates, no tree {pass_best:.2}/{pass_med:.2} ms; \
             (b) 2,000-line tree, no candidates {tree_best:.2}/{tree_med:.2} ms; \
             (c) both {all_best:.2}/{all_med:.2} ms; \
             (d) 40-line tree, 50 candidates {few_best:.2}/{few_med:.2} ms \
             — §9.1's tick budget is {TUI_TICK_BUDGET_MS} ms, and every row here is a LOWER \
             bound on a kernel replan: steps 5-8 are not written and there is no planner op \
             on the wire.  The request of (c) is {} KiB, and the rows MOVE WITH THE CALLER'S \
             PROFILE — measured 2x between `opt-level = 0` and `opt-level = 1` — so quote them \
             with the profile beside them or not at all",
            big.len() / 1024
        );
    });
}
